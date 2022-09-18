use std::{collections::BTreeSet, iter::successors, cmp::max};

use ark_ff::PrimeField;
use ark_poly::{
    univariate::DensePolynomial, EvaluationDomain, GeneralEvaluationDomain, Polynomial,
    UVPolynomial,
};
use ark_std::rand::Rng;

use crate::{
    concrete_oracle::{OracleType, ProverConcreteOracle},
    error::Error,
    iop::{verifier::VerifierFirstMsg, IOPforPolyIdentity},
    vo::{
        query::{InstanceQuery, Query, WitnessQuery},
        VirtualOracle,
    },
};

// Note: To keep flexible vanishing polynomial should not be strictly domain.vanishing_polynomial
// For example consider https://hackmd.io/1DaroFVfQwySwZPHMoMdBg?view where we remove some roots from Zh

/// State of the prover
pub struct ProverState<'a, F: PrimeField> {
    pub(crate) witness_oracles: Vec<ProverConcreteOracle<F>>,
    pub(crate) instance_oracles: Vec<ProverConcreteOracle<F>>,
    pub(crate) vos: &'a Vec<Box<dyn VirtualOracle<F>>>,
    pub(crate) domain: GeneralEvaluationDomain<F>,
    pub(crate) vanishing_polynomial: DensePolynomial<F>,
    pub(crate) quotient_chunks: Option<Vec<DensePolynomial<F>>>,
}

impl<F: PrimeField> IOPforPolyIdentity<F> {
    pub fn prover_first_round<R: Rng>(
        state: &mut ProverState<F>,
        rng: &mut R,
    ) -> Result<(), Error> {
        // 1. Get all different witness queries
        let wtns_queries: BTreeSet<WitnessQuery> = state
            .vos
            .iter()
            .map(|vo| vo.get_wtns_queries())
            .flatten()
            .map(|query| query.clone())
            .collect::<Vec<WitnessQuery>>()
            .iter()
            .map(|wtns_query| wtns_query.clone())
            .collect();

        let instance_queries: BTreeSet<InstanceQuery> = state
            .vos
            .iter()
            .map(|vo| vo.get_instance_queries())
            .flatten()
            .map(|query| query.clone())
            .collect::<Vec<InstanceQuery>>()
            .iter()
            .map(|instance_query| instance_query.clone())
            .collect();

        // 2. Assign rotations to matching concrete oracles
        for query in &wtns_queries {
            if query.index >= state.witness_oracles.len() {
                return Err(Error::WtnsQueryIndexOutOfBounds(query.index));
            }

            state.witness_oracles[query.index].register_rotation(query.rotation.clone());
        }

        for query in &instance_queries {
            if query.index >= state.instance_oracles.len() {
                return Err(Error::InstanceQueryIndexOutOfBounds(query.index));
            }

            state.instance_oracles[query.index].register_rotation(query.rotation.clone());
        }

        // 3. Mask wtns oracles
        for oracle in &mut state.witness_oracles {
            oracle.mask(&state.vanishing_polynomial, rng);
        }

        Ok(())
    }

    pub fn prover_second_round(
        verifier_msg: &VerifierFirstMsg<F>,
        state: &mut ProverState<F>,
        srs_size: usize,
    ) -> Result<(), Error> {
        // 1. compute quotient degree
        let mut max_degree = 0;
        for vo in state.vos {
            let wtns_degrees: Vec<usize> = vo.get_wtns_queries().iter().map(|query| {
                state.witness_oracles[query.index].get_degree()
            }).collect();

            let instance_degrees: Vec<usize> = vo.get_instance_queries().iter().map(|query| {
                state.instance_oracles[query.index].get_degree()
            }).collect();

            let vo_degree = vo.compute_degree(&wtns_degrees, &instance_degrees);
            max_degree = max(max_degree, vo_degree);
        }   

        let quotient_degree = max_degree - state.vanishing_polynomial.degree();

        // 2. Compute extended domain
        let extended_domain = GeneralEvaluationDomain::new(quotient_degree).unwrap();
        let scaling_ratio = extended_domain.size() / state.domain.size();

        // 3. Compute extended evals of each oracle
        for oracle in &mut state.witness_oracles {
            oracle.compute_extended_evals(extended_domain);
        }

        for oracle in &mut state.instance_oracles {
            oracle.compute_extended_evals(extended_domain);
        }

        let powers_of_alpha: Vec<F> = successors(Some(F::one()), |alpha_i| {
            Some(*alpha_i * verifier_msg.alpha)
        })
        .take(state.vos.len())
        .collect();

        let mut nominator_evals = vec![F::zero(); extended_domain.size()];
        for i in 0..extended_domain.size() {
            for (vo_index, vo) in state.vos.iter().enumerate() {
                let wtns_evals = vo
                    .get_wtns_queries()
                    .iter()
                    .map(|query| {
                        IOPforPolyIdentity::query_concrete_oracle_in_instantiation(
                            state,
                            query,
                            i,
                            scaling_ratio,
                            extended_domain.size(),
                        )
                    })
                    .collect::<Result<Vec<F>, Error>>()?;

                let instance_evals = vo
                    .get_instance_queries()
                    .iter()
                    .map(|query| {
                        IOPforPolyIdentity::query_concrete_oracle_in_instantiation(
                            state,
                            query,
                            i,
                            scaling_ratio,
                            extended_domain.size(),
                        )
                    })
                    .collect::<Result<Vec<F>, Error>>()?;

                let x = extended_domain.element(i);
                let vo_constraint = vo.constraint_function(x, &wtns_evals, &instance_evals);
                nominator_evals[i] += powers_of_alpha[vo_index] * vo_constraint;
            }
        }

        let mut zh_evals = extended_domain.coset_fft(&state.vanishing_polynomial);
        ark_ff::batch_inversion(&mut zh_evals);

        let quotient_evals: Vec<_> = nominator_evals
            .iter()
            .zip(zh_evals.iter())
            .map(|(&nom, &denom)| nom * denom)
            .collect();

        let quotient =
            DensePolynomial::from_coefficients_slice(&extended_domain.coset_ifft(&quotient_evals));
        state.quotient_chunks = Some(
            quotient
                .coeffs
                .chunks(srs_size)
                .map(|chunk| DensePolynomial::from_coefficients_slice(chunk))
                .collect(),
        );

        Ok(())
    }

    fn query_concrete_oracle_in_instantiation(
        state: &ProverState<F>,
        query: &impl Query,
        row: usize,
        scaling_ratio: usize,
        extended_domain_size: usize,
    ) -> Result<F, Error> {
        let index = query.get_index();
        let query_result: Result<F, Error> = match query.get_type() {
            OracleType::Witness => {
                if index > state.witness_oracles.len() {
                    return Err(Error::WtnsQueryIndexOutOfBounds(index));
                }

                state.witness_oracles[index].query_in_instantiation_context(
                    &query.get_rotation(),
                    row,
                    scaling_ratio,
                    extended_domain_size,
                )
            }
            OracleType::Instance => {
                if index > state.instance_oracles.len() {
                    return Err(Error::InstanceQueryIndexOutOfBounds(index));
                }

                state.instance_oracles[index].query_in_instantiation_context(
                    &query.get_rotation(),
                    row,
                    scaling_ratio,
                    extended_domain_size,
                )
            }
        };

        query_result
    }

    fn query_concrete_oracle_in_opening(
        state: &ProverState<F>,
        query: &impl Query,
        challenge: &F,
        domain_size: usize,
    ) -> Result<F, Error> {
        let index = query.get_index();
        let query_result: Result<F, Error> = match query.get_type() {
            OracleType::Witness => {
                if index > state.witness_oracles.len() {
                    return Err(Error::WtnsQueryIndexOutOfBounds(index));
                }

                state.witness_oracles[index].query_in_opening_context(
                    &query.get_rotation(),
                    challenge,
                    domain_size,
                )
            }
            OracleType::Instance => {
                if index > state.instance_oracles.len() {
                    return Err(Error::InstanceQueryIndexOutOfBounds(index));
                }

                state.instance_oracles[index].query_in_opening_context(
                    &query.get_rotation(),
                    challenge,
                    domain_size,
                )
            }
        };

        query_result
    }
}
