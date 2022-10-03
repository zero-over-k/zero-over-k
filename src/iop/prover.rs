use std::{cmp::max, collections::BTreeSet, iter::successors};

use ark_ff::PrimeField;
use ark_poly::{
    univariate::DensePolynomial, EvaluationDomain, GeneralEvaluationDomain, Polynomial,
    UVPolynomial,
};
use ark_poly_commit::LabeledPolynomial;
use ark_std::rand::Rng;

use crate::{
    concrete_oracle::{OracleType, ProverConcreteOracle, Queriable, QueryContext, QueryPoint},
    iop::error::Error,
    iop::{verifier::VerifierFirstMsg, IOPforPolyIdentity},
    vo::{
        query::{InstanceQuery, Query, Rotation, WitnessQuery},
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
}

impl<F: PrimeField> IOPforPolyIdentity<F> {
    // NOTE: consider having indexed concrete oracles by initializing evals_at_coset_of_extended_domain (ex. selector polynomials)
    pub fn init_prover<'a>(
        concrete_oracles: &[ProverConcreteOracle<F>],
        vos: &'a Vec<Box<dyn VirtualOracle<F>>>,
        domain_size: usize,
        vanishing_polynomial: &DensePolynomial<F>,
    ) -> ProverState<'a, F> {
        let mut witness_oracles = vec![];
        let mut instance_oracles = vec![];

        // TODO: consider keeping pointers to oracle in state
        for oracle in concrete_oracles {
            match oracle.oracle_type {
                OracleType::Witness => witness_oracles.push(oracle.clone()), 
                OracleType::Instance => instance_oracles.push(oracle.clone())
            }
        }

        let domain = GeneralEvaluationDomain::new(domain_size).unwrap();

        ProverState {
            witness_oracles: witness_oracles.clone(),
            instance_oracles: instance_oracles.clone(),
            vos: vos,
            domain,
            vanishing_polynomial: vanishing_polynomial.clone(),
        }
    }
    pub fn prover_first_round<'a, R: Rng>(
        state: &'a mut ProverState<F>,
        rng: &mut R,
    ) -> Result<Vec<ProverConcreteOracle<F>>, Error> {
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
        for oracle in state.witness_oracles.iter_mut() {
            oracle.mask(&state.vanishing_polynomial, rng);
        }

        Ok(state.witness_oracles.clone())
    }

    pub fn prover_second_round(
        verifier_msg: &VerifierFirstMsg<F>,
        state: &mut ProverState<F>,
        srs_size: usize,
    ) -> Result<Vec<ProverConcreteOracle<F>>, Error> {
        let wnts_get_degree_fn = |query: &WitnessQuery| {
            let oracle = &state.witness_oracles[query.get_index()];
            oracle.get_degree()
        };

        let instance_get_degree_fn = |query: &InstanceQuery| {
            let oracle = &state.instance_oracles[query.get_index()];
            oracle.get_degree()
        };

        // 1. compute quotient degree
        let mut max_degree = 0;
        for vo in state.vos {
            let vo_degree = vo
                .get_expression()
                .degree(&wnts_get_degree_fn, &instance_get_degree_fn);
            max_degree = max(max_degree, vo_degree);
        }

        let quotient_degree = max_degree - state.vanishing_polynomial.degree();
        println!("quotient_degree {}", quotient_degree);


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

        let mut query_context = QueryContext::Instantiation(
            scaling_ratio,
            extended_domain.size(),
            QueryPoint::<F>::Omega(0),
        );

        for i in 0..extended_domain.size() {
            query_context.replace_omega(i);
            for (vo_index, vo) in state.vos.iter().enumerate() {
                let vo_evaluation = vo.get_expression().evaluate::<F>(
                    &|x: F| x,
                    &|query: &WitnessQuery| {
                        let oracle = &state.witness_oracles[query.get_index()];
                        oracle.query(&query.rotation, &query_context)
                    },
                    &|query: &InstanceQuery| {
                        let oracle = &state.instance_oracles[query.get_index()];
                        oracle.query(&query.rotation, &query_context)
                    },
                    &|x: F| -x,
                    &|x: F, y: F| x + y,
                    &|x: F, y: F| x * y,
                    &|x: F, y: F| x * y,
                );

                nominator_evals[i] += powers_of_alpha[vo_index] * vo_evaluation;
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

        let quotient_chunks: Vec<ProverConcreteOracle<F>> = quotient
            .coeffs
            .chunks(srs_size)
            .enumerate()
            .map(|(i, chunk)| {
                let poly = DensePolynomial::from_coefficients_slice(chunk);
                ProverConcreteOracle {
                    label: format!("t_{}", i).to_string(),
                    poly,
                    evals_at_coset_of_extended_domain: None,
                    oracle_type: OracleType::Witness,
                    queried_rotations: vec![Rotation::curr()],
                    should_mask: false,
                }
            })
            .collect();

        // state.quotient_chunks = Some(quotient_chunks.clone());

        // let prover_second_oracles = ProverSecondOracles {
        //     quotient_chunks: quotient_chunks
        //         .iter()
        //         .enumerate()
        //         .map(|(i, chunk)| {
        //             LabeledPolynomial::new(format!("t_{}", i), chunk.clone(), None, None)
        //         })
        //         .collect(),
        // };

        Ok(quotient_chunks)
    }
}
