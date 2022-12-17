use std::{
    collections::{BTreeMap, BTreeSet},
    iter::successors,
};

use ark_ff::PrimeField;
use ark_poly::{
    univariate::DensePolynomial, EvaluationDomain, GeneralEvaluationDomain,
    UVPolynomial,
};
use ark_std::rand::Rng;

use crate::{
    commitment::HomomorphicCommitment,
    data_structures::{Index, ProverPreprocessedInput, VerifierKey},
    lookup::{subset_equality::SubsetEqualityArgument, LookupArgument},
    oracles::{
        instance::InstanceProverOracle,
        query::OracleType,
        rotation::Rotation,
        traits::{ConcreteOracle, Instantiable},
        witness::{WitnessProverOracle, WitnessVerifierOracle},
    },
    permutation::PermutationArgument,
    piop::error::Error as PiopError,
    piop::{verifier::VerifierFirstMsg, PIOPforPolyIdentity},
    vo::VirtualOracle,
};

use super::verifier::{VerifierLookupAggregationRound, VerifierPermutationMsg};

pub type LookupProverOracles<F> = (
    WitnessProverOracle<F>, //a
    WitnessProverOracle<F>, //s
    WitnessProverOracle<F>, //a_prime
    WitnessProverOracle<F>, //s_prime
);

pub type LookupVerifierOracles<F, PC> = (
    WitnessVerifierOracle<F, PC>, //a
    WitnessVerifierOracle<F, PC>, //s
    WitnessVerifierOracle<F, PC>, //a_prime
    WitnessVerifierOracle<F, PC>, //s_prime
);

// Note: To keep flexible vanishing polynomial should not be strictly domain.vanishing_polynomial
// For example consider https://hackmd.io/1DaroFVfQwySwZPHMoMdBg?view where we remove some roots from Zh

// #[derive(Clone)]
/// State of the prover
pub struct ProverState<'a, F: PrimeField> {
    pub(crate) witness_oracles_mapping: BTreeMap<String, usize>, // TODO: introduce &str here maybe
    pub(crate) instance_oracles_mapping: BTreeMap<String, usize>,
    pub(crate) fixed_oracles_mapping: BTreeMap<String, usize>,
    pub(crate) table_oracles_mapping: BTreeMap<String, usize>,
    pub(crate) witness_oracles: &'a [WitnessProverOracle<F>],
    pub(crate) instance_oracles: &'a [InstanceProverOracle<F>],
    pub(crate) z_polys: Option<Vec<WitnessProverOracle<F>>>,
    pub(crate) lookup_polys: Option<Vec<LookupProverOracles<F>>>,
    pub(crate) lookup_z_polys: Option<Vec<WitnessProverOracle<F>>>,
    pub(crate) oracles_to_copy: Vec<&'a WitnessProverOracle<F>>,
    pub(crate) vos: &'a [&'a dyn VirtualOracle<F>],

    pub(crate) domain: GeneralEvaluationDomain<F>,
    pub(crate) quotient_chunks: Option<Vec<WitnessProverOracle<F>>>,
}

impl<F: PrimeField, PC: HomomorphicCommitment<F>> PIOPforPolyIdentity<F, PC> {
    // Aux funcs for `evaluate`
    fn ident(x: F) -> Result<F, PiopError> {
        Ok(x)
    }
    fn neg(x: Result<F, PiopError>) -> Result<F, PiopError> {
        x.map(|x_val| -x_val)
    }
    fn add(
        x: Result<F, PiopError>,
        y: Result<F, PiopError>,
    ) -> Result<F, PiopError> {
        x.and_then(|x_val| y.map(|y_val| x_val + y_val))
    }
    fn mul(
        x: Result<F, PiopError>,
        y: Result<F, PiopError>,
    ) -> Result<F, PiopError> {
        x.and_then(|x_val| y.map(|y_val| x_val * y_val))
    }
    fn scale(x: Result<F, PiopError>, y: F) -> Result<F, PiopError> {
        x.map(|x_val| x_val * y)
    }

    pub fn init_prover<'a>(
        witness_oracles: &'a [WitnessProverOracle<F>],
        instance_oracles: &'a [InstanceProverOracle<F>],
        vos: &'a [&'a dyn VirtualOracle<F>],
        domain_size: usize,
        preprocessed: &ProverPreprocessedInput<F, PC>,
    ) -> ProverState<'a, F> {
        let domain = GeneralEvaluationDomain::new(domain_size).unwrap();

        let witness_oracles_mapping = witness_oracles
            .iter()
            .enumerate()
            .map(|(i, oracle)| (oracle.get_label(), i))
            .collect();
        let instance_oracles_mapping = instance_oracles
            .iter()
            .enumerate()
            .map(|(i, oracle)| (oracle.get_label(), i))
            .collect();
        let fixed_oracles_mapping = preprocessed
            .fixed_oracles
            .iter()
            .enumerate()
            .map(|(i, oracle)| (oracle.get_label(), i))
            .collect();
        let table_oracles_mapping = preprocessed
            .table_oracles
            .iter()
            .enumerate()
            .map(|(i, oracle)| (oracle.get_label(), i))
            .collect();

        let oracles_to_copy: Vec<&WitnessProverOracle<F>> = witness_oracles
            .iter()
            .filter(|&oracle| oracle.should_permute)
            .collect();

        ProverState {
            witness_oracles_mapping,
            instance_oracles_mapping,
            fixed_oracles_mapping,
            table_oracles_mapping,
            witness_oracles,
            instance_oracles,
            z_polys: None,
            lookup_polys: None,
            lookup_z_polys: None,
            oracles_to_copy,
            vos,
            domain,
            quotient_chunks: None,
        }
    }

    pub fn prover_permutation_round<R: Rng>(
        permutation_msg: &VerifierPermutationMsg<F>,
        state: &mut ProverState<F>,
        permutation_argument: &PermutationArgument<F>,
        preprocessed: &ProverPreprocessedInput<F, PC>,
        extended_coset_domain: &GeneralEvaluationDomain<F>,
        zk_rng: &mut R,
    ) -> Vec<WitnessProverOracle<F>> {
        // if nothing to copy just return empty vector
        if state.oracles_to_copy.is_empty() {
            state.z_polys = Some(vec![]);
            return vec![];
        }
        let z_polys = permutation_argument.construct_agg_polys(
            &state.oracles_to_copy,
            &preprocessed.permutation_oracles,
            permutation_msg.beta,
            permutation_msg.gamma,
            &state.domain,
            extended_coset_domain,
            zk_rng,
        );

        state.z_polys = Some(z_polys.clone());
        z_polys
    }

    pub fn prover_lookup_round<R: Rng>(
        lookup_aggregation_msg: &VerifierLookupAggregationRound<F>,
        state: &mut ProverState<F>,
        preprocessed: &ProverPreprocessedInput<F, PC>,
        index: &Index<F>,
        zk_rng: &mut R,
    ) -> Result<Vec<LookupProverOracles<F>>, PiopError> {
        let lookup_polys: Vec<_> = index
            .lookups
            .iter()
            .enumerate()
            .map(|(lookup_index, lookup_vo)| -> Result<_, PiopError> {
                LookupArgument::construct_a_and_s_polys_prover(
                    &state.witness_oracles_mapping,
                    &state.instance_oracles_mapping,
                    &state.fixed_oracles_mapping,
                    &state.table_oracles_mapping,
                    state.witness_oracles,
                    state.instance_oracles,
                    &preprocessed.fixed_oracles,
                    &preprocessed.table_oracles,
                    index.usable_rows,
                    lookup_index,
                    lookup_vo.get_expressions()?,
                    lookup_vo.get_table_queries()?,
                    lookup_aggregation_msg.theta,
                    &state.domain,
                    &index.extended_coset_domain,
                    zk_rng,
                )
            })
            .collect::<Result<_, _>>()?;

        // In order: (a, s, a_prime, s_prime)
        state.lookup_polys = Some(lookup_polys.clone());
        Ok(lookup_polys)
    }

    pub fn prover_lookup_subset_equality_round<R: Rng>(
        permutation_msg: &VerifierPermutationMsg<F>,
        // In order: (a, s, a_prime, s_prime)
        lookup_polys: &[LookupProverOracles<F>],
        state: &mut ProverState<F>,
        index: &Index<F>,
        zk_rng: &mut R,
    ) -> Vec<WitnessProverOracle<F>> {
        let lookup_z_polys: Vec<_> = lookup_polys
            .iter()
            .enumerate()
            .map(|(lookup_index, lookup_polys)| {
                SubsetEqualityArgument::construct_agg_poly(
                    lookup_polys,
                    permutation_msg.beta,
                    permutation_msg.gamma,
                    lookup_index,
                    index.usable_rows,
                    &state.domain,
                    &index.extended_coset_domain,
                    zk_rng,
                )
            })
            .collect();

        state.lookup_z_polys = Some(lookup_z_polys.clone());
        lookup_z_polys
    }

    pub fn prover_quotient_round(
        verifier_permutation_msg: &VerifierPermutationMsg<F>,
        verifier_msg: &VerifierFirstMsg<F>,
        state: &mut ProverState<F>,
        vk: &VerifierKey<F, PC>,
        preprocessed: &ProverPreprocessedInput<F, PC>,
    ) -> Result<Vec<WitnessProverOracle<F>>, PiopError> {
        let powers_of_alpha: Vec<F> = successors(Some(F::one()), |alpha_i| {
            Some(*alpha_i * verifier_msg.alpha)
        })
        .take(state.vos.len())
        .collect();

        let mut numerator_evals =
            vec![F::zero(); vk.index_info.extended_coset_domain.size()];

        let _lookup_evals =
            vec![F::zero(); vk.index_info.extended_coset_domain.size()];

        let z_polys = state.z_polys.as_ref().expect("Z polys are not in state");
        let lookup_polys = state
            .lookup_polys
            .as_ref()
            .expect("lookup polys are not in state");
        let lookup_z_polys = state
            .lookup_z_polys
            .as_ref()
            .expect("lookup aggregation polys are not in state");

        let number_of_permutation_alphas = vk
            .index_info
            .permutation_argument
            .number_of_alphas(z_polys.len());

        // start from next of last power of alpha
        let permutation_begin_with =
            *powers_of_alpha.last().unwrap() * verifier_msg.alpha;
        let permutation_alphas: Vec<F> =
            successors(Some(permutation_begin_with), |alpha_i| {
                Some(*alpha_i * verifier_msg.alpha)
            })
            .take(number_of_permutation_alphas)
            .collect();

        // For each lookup argument we need 5 alphas
        // Again begin with last alpha after permutation argument
        let lookups_begin_with = if let Some(alpha) = permutation_alphas.last()
        {
            *alpha
        } else {
            *powers_of_alpha.last().unwrap()
        };

        let lookup_alphas: Vec<F> =
            successors(Some(lookups_begin_with), |alpha_i| {
                Some(*alpha_i * verifier_msg.alpha)
            })
            .take(5 * vk.index_info.lookups.len())
            .collect();

        let lookup_alpha_chunks: Vec<&[F]> = lookup_alphas.chunks(5).collect();

        let domain_size = state.domain.size();
        let mut l0_evals = vec![F::zero(); domain_size];
        l0_evals[0] = F::one();
        let l0 = DensePolynomial::from_coefficients_slice(
            &state.domain.ifft(&l0_evals),
        );
        let l0_coset_evals = vk.index_info.extended_coset_domain.coset_fft(&l0);

        let mut lu_evals = vec![F::zero(); domain_size];
        lu_evals[vk.index_info.permutation_argument.usable_rows] = F::one();
        let lu = DensePolynomial::from_coefficients_slice(
            &state.domain.ifft(&lu_evals),
        );
        let lu_coset_evals = vk.index_info.extended_coset_domain.coset_fft(&lu);

        // for i in 0..vk.index_info.extended_coset_domain.size() {
        for (i, numerator_eval) in numerator_evals.iter_mut().enumerate() {
            for (vo_index, vo) in state.vos.iter().enumerate() {
                let vo_evaluation = vo.get_expression()?.evaluate(
                    &Self::ident,
                    &|query| match query.oracle_type {
                        OracleType::Witness => {
                            match state
                                .witness_oracles_mapping
                                .get(&query.label)
                            {
                                Some(index) => state.witness_oracles[*index]
                                    .query_in_coset(i, query.rotation),
                                None => Err(PiopError::MissingWitnessOracle(
                                    query.label.clone(),
                                )),
                            }
                        }
                        OracleType::Instance => {
                            match state
                                .instance_oracles_mapping
                                .get(&query.label)
                            {
                                Some(index) => state.instance_oracles[*index]
                                    .query_in_coset(i, query.rotation),
                                None => Err(PiopError::MissingInstanceOracle(
                                    query.label.clone(),
                                )),
                            }
                        }
                        OracleType::Fixed => {
                            match state.fixed_oracles_mapping.get(&query.label)
                            {
                                Some(index) => preprocessed.fixed_oracles
                                    [*index]
                                    .query_in_coset(i, query.rotation),
                                None => Err(PiopError::MissingFixedOracle(
                                    query.label.clone(),
                                )),
                            }
                        }
                    },
                    &Self::neg,
                    &Self::add,
                    &Self::mul,
                    &Self::scale,
                );

                *numerator_eval += powers_of_alpha[vo_index] * vo_evaluation?;
            }

            // Permutation argument
            // If there are no oracles to enforce copy constraints on, we just return zero
            *numerator_eval += if !state.oracles_to_copy.is_empty() {
                vk.index_info
                    .permutation_argument
                    .instantiate_argument_at_omega_i(
                        &l0_coset_evals,
                        &lu_coset_evals,
                        &preprocessed.q_blind,
                        &state.oracles_to_copy,
                        &preprocessed.permutation_oracles,
                        z_polys,
                        i,
                        vk.index_info.extended_coset_domain.element(i),
                        verifier_permutation_msg.beta,
                        verifier_permutation_msg.gamma,
                        &state.domain,
                        &permutation_alphas,
                    )?
            } else {
                F::zero()
            };

            for ((lookup_oracles, z), &alpha_powers) in lookup_polys
                .iter()
                .zip(lookup_z_polys.iter())
                .zip(lookup_alpha_chunks.iter())
            {
                *numerator_eval +=
                    LookupArgument::instantiate_argument_at_omega_i(
                        &l0_coset_evals,
                        &lu_coset_evals,
                        &preprocessed.q_blind,
                        lookup_oracles,
                        z,
                        verifier_permutation_msg.beta,
                        verifier_permutation_msg.gamma,
                        i,
                        alpha_powers,
                    )?
            }
        }

        let quotient_evals: Vec<_> = numerator_evals
            .iter()
            .zip(vk.zh_inverses_over_coset.iter())
            .map(|(&nom, &denom)| nom * denom)
            .collect();

        let quotient = DensePolynomial::from_coefficients_slice(
            &vk.index_info
                .extended_coset_domain
                .coset_ifft(&quotient_evals),
        );

        let mut quotient_coeffs = Vec::from(quotient.coeffs());
        let padding_size =
            vk.index_info.extended_coset_domain.size() - quotient_coeffs.len();
        if padding_size > 0 {
            quotient_coeffs.extend(vec![F::zero(); padding_size]);
        }

        let quotient_chunks: Vec<WitnessProverOracle<F>> = quotient_coeffs
            .chunks(state.domain.size())
            .enumerate()
            .map(|(i, chunk)| {
                let poly = DensePolynomial::from_coefficients_slice(chunk);
                WitnessProverOracle {
                    label: format!("quotient_chunk_{}", i),
                    evals: state.domain.fft(&poly),
                    poly,
                    evals_at_coset_of_extended_domain: None,
                    queried_rotations: BTreeSet::from([Rotation::curr()]),
                    should_permute: false,
                }
            })
            .collect();

        state.quotient_chunks = Some(quotient_chunks.clone());
        Ok(quotient_chunks)
    }
}

#[cfg(test)]
mod test {
    use crate::commitment::{HomomorphicCommitment, KZG10};
    use ark_bls12_381::{Bls12_381, Fr as F};
    use ark_ff::{One, UniformRand};
    use ark_poly::{univariate::DensePolynomial, Polynomial, UVPolynomial};
    use ark_poly_commit::{
        LabeledCommitment, LabeledPolynomial, PCUniversalParams,
        PolynomialCommitment,
    };
    use ark_std::test_rng;

    type PC = KZG10<Bls12_381>;

    #[test]
    fn test_rands_homomorphism() {
        let max_degree = 17;
        let mut rng = test_rng();

        let poly_degree = 10;
        let srs = PC::setup(max_degree, None, &mut rng).unwrap();

        let (committer_key, verifier_key) =
            PC::trim(&srs, srs.max_degree(), 1, None).unwrap();

        let p = DensePolynomial::<F>::rand(poly_degree, &mut rng);
        let p = LabeledPolynomial::new("p".to_string(), p, None, Some(1));
        let q = DensePolynomial::<F>::rand(poly_degree, &mut rng);
        let q = LabeledPolynomial::new("q".to_string(), q, None, Some(1));

        let polys = [p.clone(), q.clone()];

        let (comms, rands) =
            PC::commit(&committer_key, polys.iter(), Some(&mut rng)).unwrap();

        let challenge = F::rand(&mut rng);
        let x1 = F::rand(&mut rng);

        let r = p.polynomial().clone() + q.polynomial() * x1;
        let value = r.evaluate(&challenge);

        let r = LabeledPolynomial::new("r".to_string(), r, None, Some(1));

        let r_comm = PC::add(
            comms[0].commitment(),
            &PC::scale_com(comms[1].commitment(), x1),
        );
        let r_comm = LabeledCommitment::new("r_comm".to_string(), r_comm, None);
        let r_rand = PC::add_rands(&rands[0], &PC::scale_rand(&rands[1], x1));

        let proof = PC::open(
            &committer_key,
            &[r],
            &[r_comm],
            &challenge,
            F::one(),
            &[r_rand],
            Some(&mut rng),
        )
        .unwrap();

        let r_comm = PC::add(
            comms[0].commitment(),
            &PC::scale_com(comms[1].commitment(), x1),
        );
        let r_comm = LabeledCommitment::new("r_comm".to_string(), r_comm, None);

        let res = PC::check(
            &verifier_key,
            &[r_comm],
            &challenge,
            vec![value],
            &proof,
            F::one(),
            Some(&mut rng),
        )
        .unwrap();
        assert!(res);
    }
}
