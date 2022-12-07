use std::{cmp::max, collections::BTreeMap, iter, marker::PhantomData};

use ark_ff::PrimeField;
use ark_poly::{
    univariate::DensePolynomial, EvaluationDomain, GeneralEvaluationDomain,
    Polynomial,
};

use crate::{
    commitment::HomomorphicCommitment,
    data_structures::{Index, PermutationInfo, VerifierKey},
    error::Error,
    lookup::LookupArgument,
    oracles::{
        query::OracleType,
        traits::{FixedOracle, InstanceOracle, WitnessOracle},
    },
    permutation::PermutationArgument,
    piop::error::Error as PiopError,
    util::compute_vanishing_poly_over_coset,
    vo::{LookupVirtualOracle, VirtualOracle},
};

/*
    We want to support both Plonkish like zero over K checks, where each gate is separated with
    selector, ex: (q_1, gate_1), (q_2, gate_2), and also arbitrary polynomial constraints,
    (ex. https://eprint.iacr.org/2021/1342.pdf look at proof of functional relation)
    where there is no concept of selector.

    There are multiple ways of how to blind some oracles.

    1. In Plonkish like style we can reserve some t rows for blinding and simply when constructing
    vanishing argument all selectors are zero at that t rows.

    2. When there are no selectors we can still use some t rows for blinding, but now instead of
    checking that something vanishes on

    zH = X^n - 1, we can check that it vanishes on zH = (X^n - 1) / prod{i in last [t]} (x - w_i)
*/
pub struct Indexer<F: PrimeField, PC: HomomorphicCommitment<F>> {
    _f: PhantomData<F>,
    _pc: PhantomData<PC>,
}

impl<F: PrimeField, PC: HomomorphicCommitment<F>> Indexer<F, PC> {
    fn compute_quotient_degree(
        witness_oracles: &[&mut impl WitnessOracle<F>],
        instance_oracles: &[&mut impl InstanceOracle<F>],
        fixed_oracles: &[&mut impl FixedOracle<F>],
        witness_oracles_mapping: &BTreeMap<String, usize>,
        instance_oracles_mapping: &BTreeMap<String, usize>,
        fixed_oracles_mapping: &BTreeMap<String, usize>,
        vos: &[&dyn VirtualOracle<F>],
        domain_size: usize,
        z_h_degree: usize,
    ) -> Result<usize, Error<PC::Error>> {
        let mut max_degree = 0;
        for &vo in vos {
            let vo_degree =
                vo.get_expression()?.degree(&|query| -> Result<_, _> {
                    match query.oracle_type {
                        OracleType::Witness => {
                            match witness_oracles_mapping.get(&query.label) {
                                Some(index) => Ok(witness_oracles[*index]
                                    .get_degree(domain_size)),
                                None => Err(PiopError::MissingWitnessOracle(
                                    query.label.clone(),
                                )),
                            }
                        }
                        OracleType::Instance => {
                            match instance_oracles_mapping.get(&query.label) {
                                Some(index) => Ok(instance_oracles[*index]
                                    .get_degree(domain_size)),
                                None => Err(PiopError::MissingInstanceOracle(
                                    query.label.clone(),
                                )),
                            }
                        }
                        OracleType::Fixed => {
                            match fixed_oracles_mapping.get(&query.label) {
                                Some(index) => Ok(fixed_oracles[*index]
                                    .get_degree(domain_size)),
                                None => Err(PiopError::MissingFixedOracle(
                                    query.label.clone(),
                                )),
                            }
                        }
                    }
                });
            max_degree = max(max_degree, vo_degree?);
        }

        Ok(max_degree - z_h_degree)
    }

    fn compute_zh_evals(
        domain: &GeneralEvaluationDomain<F>,
        extended_coset_domain: &GeneralEvaluationDomain<F>,
        z_h: DensePolynomial<F>,
    ) -> Vec<F> {
        assert!(domain.size() <= extended_coset_domain.size());
        /*
        Consider case when simple mul over whole domain is being checked: a * b - c = 0 and zH = X^n - 1,
        extended_coset_domain will be exactly domain and zH.coset_fft() will not work since zH.degree() = 16 > 15
        */
        let domain_size = domain.size();
        let vanish_dense: DensePolynomial<F> =
            domain.vanishing_polynomial().into();
        let zh_inverses_over_coset = if vanish_dense == z_h
            && domain_size == extended_coset_domain.size()
        {
            let zh_eval = domain
                .evaluate_vanishing_polynomial(F::multiplicative_generator())
                .inverse()
                .unwrap();
            iter::repeat(zh_eval).take(domain_size).collect()
        } else if vanish_dense == z_h {
            // extended_coset_domain must be bigger then original domain
            let mut zh_evals = compute_vanishing_poly_over_coset(
                extended_coset_domain.clone(),
                domain_size as u64,
            );
            ark_ff::batch_inversion(&mut zh_evals);
            zh_evals
        } else {
            let mut zh_evals = extended_coset_domain.coset_fft(&z_h);
            ark_ff::batch_inversion(&mut zh_evals);
            zh_evals
        };

        zh_inverses_over_coset
    }

    pub fn index<'a>(
        vk: &PC::VerifierKey,
        vos: &[&dyn VirtualOracle<F>],
        lookups: Vec<&'a dyn LookupVirtualOracle<F>>,
        witness_oracles: &[&mut impl WitnessOracle<F>],
        instance_oracles: &[&mut impl InstanceOracle<F>],
        fixed_oracles: &[&mut impl FixedOracle<F>],
        domain: GeneralEvaluationDomain<F>,
        z_h: &DensePolynomial<F>,
        permutation_info: PermutationInfo<F>,
        usable_rows: usize,
    ) -> Result<VerifierKey<'a, F, PC>, Error<PC::Error>> {
        let witness_oracles_mapping: BTreeMap<String, usize> = witness_oracles
            .iter()
            .enumerate()
            .map(|(i, oracle)| (oracle.get_label(), i))
            .collect();

        let instance_oracles_mapping: BTreeMap<String, usize> =
            instance_oracles
                .iter()
                .enumerate()
                .map(|(i, oracle)| (oracle.get_label(), i))
                .collect();

        let fixed_oracles_mapping: BTreeMap<String, usize> = fixed_oracles
            .iter()
            .enumerate()
            .map(|(i, oracle)| (oracle.get_label(), i))
            .collect();

        let quotient_degree: usize = Self::compute_quotient_degree(
            witness_oracles,
            instance_oracles,
            &fixed_oracles,
            &witness_oracles_mapping,
            &instance_oracles_mapping,
            &fixed_oracles_mapping,
            vos,
            domain.size(),
            z_h.degree(),
        )?;

        // TODO: we can introduce next power of 2 check here instead of creating domain and then dividing
        let extended_coset_domain =
            GeneralEvaluationDomain::<F>::new(quotient_degree).unwrap();

        if extended_coset_domain.size() < domain.size() {
            return Err(Error::QuotientTooSmall);
        }

        // it is possible that there are no oracles to permute
        let num_of_oracles_to_permute =
            witness_oracles.iter().fold(0usize, |sum, oracle| {
                if oracle.should_include_in_copy() {
                    sum + 1
                } else {
                    sum
                }
            });

        let scaling_factor = extended_coset_domain.size() / domain.size();
        let scaling_factor = if num_of_oracles_to_permute > 0 {
            max(
                scaling_factor,
                PermutationArgument::<F>::MINIMAL_SCALING_FACTOR,
            )
        } else {
            scaling_factor
        };

        let scaling_factor = if lookups.len() > 0 {
            max(scaling_factor, LookupArgument::<F>::MINIMAL_SCALING_FACTOR)
        } else {
            scaling_factor
        };

        // Even if there are no oracles to permute we construct permutation argument to omit Option handling on many places
        let permutation_argument =
            PermutationArgument::new(scaling_factor, &permutation_info);

        let extended_coset_domain =
            GeneralEvaluationDomain::<F>::new(scaling_factor * domain.size())
                .unwrap();

        let zh_inverses_over_coset =
            Self::compute_zh_evals(&domain, &extended_coset_domain, z_h.clone());

        let index_info = Index {
            quotient_degree,
            extended_coset_domain,
            permutation_argument,
            lookups,
            usable_rows,
        };

        let vk = VerifierKey {
            verifier_key: vk.clone(),
            index_info,
            zh_inverses_over_coset,
        };

        Ok(vk)
    }
}
