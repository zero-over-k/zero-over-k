use std::collections::{BTreeMap, BTreeSet};
use std::iter::successors;

use ark_ff::{PrimeField, Zero};
use ark_poly::univariate::DensePolynomial;
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain, Polynomial};
use ark_poly_commit::{LabeledPolynomial, PCRandomness};

use crate::commitment::HomomorphicCommitment;
use crate::multiproof::poly::construct_vanishing;
use crate::oracles::query::QueryContext;
use crate::oracles::rotation::Rotation;
use crate::oracles::traits::Instantiable;
use super::verifier::{VerifierFirstMsg, VerifierSecondMsg, VerifierThirdMsg};
use super::{PIOPError, PIOP};

// &'a Vec<Box<dyn VirtualOracle<F>>>

pub struct ProverState<'a, F: PrimeField, PC: HomomorphicCommitment<F>> {
    num_of_oracles: usize, 
    opening_sets: BTreeMap<
        BTreeSet<Rotation>,
        Vec<(&'a dyn Instantiable<F>, &'a PC::Randomness)>,
    >,
    domain: GeneralEvaluationDomain<F>,
    q_polys: Option<Vec<LabeledPolynomial<F, DensePolynomial<F>>>>,
    q_rands: Option<Vec<PC::Randomness>>,
    f_poly: Option<LabeledPolynomial<F, DensePolynomial<F>>>,
}

impl<F: PrimeField> PIOP<F> {
    // NOTE: Oracles are already masked
    pub fn init_prover<'a, PC: HomomorphicCommitment<F>>(
        oracles: &'a Vec<impl Instantiable<F>>,
        oracle_rands: &'a [PC::Randomness],
        domain_size: usize,
    ) -> Result<ProverState<'a, F, PC>, PIOPError> {
        let mut opening_sets = BTreeMap::<
            BTreeSet<Rotation>,
            Vec<(&'a dyn Instantiable<F>, &'a PC::Randomness)>,
        >::new();

        for (oracle, rand) in oracles.iter().zip(oracle_rands.iter()) {
            let oracles = opening_sets
                .entry(oracle.get_queried_rotations().clone())
                .or_insert(vec![]);
            oracles.push((oracle, rand))
        }

        let domain = GeneralEvaluationDomain::<F>::new(domain_size).unwrap();

        let state = ProverState {
            num_of_oracles: oracles.len(),
            opening_sets,
            domain,
            q_polys: None,
            q_rands: None,
            f_poly: None,
        };

        Ok(state)
    }

    pub fn prover_first_round<'a, PC: HomomorphicCommitment<F>>(
        mut state: ProverState<'a, F, PC>,
        evaluation_challenge: F,
        verifier_first_msg: &VerifierFirstMsg<F>,
    ) -> Result<
        (
            LabeledPolynomial<F, DensePolynomial<F>>,
            ProverState<'a, F, PC>,
        ),
        PIOPError,
    > {
        // Max number of oracles in one opening set are all oracles
        let x1_powers: Vec<F> = successors(Some(F::one()), |x1_i| {
            Some(*x1_i * verifier_first_msg.x1)
        })
        .take(state.num_of_oracles)
        .collect();

        let qs = state.opening_sets.iter().map(|(rotations, oracles_rands)| {
            let mut q_i = DensePolynomial::zero();
            let mut q_i_rand = PC::Randomness::empty();
            let mut q_i_evals_set = BTreeMap::<F, F>::new();

            for (i, (oracle, rand)) in oracles_rands.iter().enumerate() {
                q_i = q_i + oracle.polynomial() * x1_powers[i];
                q_i_rand = PC::add_rands(
                    &q_i_rand,
                    &PC::scale_rand(rand, x1_powers[i]),
                );
            }

            let omegas: Vec<F> = state.domain.elements().collect();
            for rotation in rotations {
                let evaluation_point = rotation
                    .compute_evaluation_point(evaluation_challenge, &omegas);
                let mut evaluation = F::zero();
                for (i, (oracle, _)) in oracles_rands.iter().enumerate() {
                    evaluation += x1_powers[i]
                        * oracle.query(&QueryContext::Challenge(evaluation_point));
                }

                let prev = q_i_evals_set.insert(evaluation_point, evaluation);
                if prev.is_some() {
                    panic!("Same evaluation point for different rotations")
                }
            }

            (q_i, q_i_rand, q_i_evals_set)
        });

        state.q_polys = Some(
            qs.clone()
                .map(|(q_poly, _, _)| {
                    LabeledPolynomial::new(
                        "q_i".to_string(),
                        q_poly,
                        None,
                        None,
                    )
                })
                .collect(),
        );

        state.q_rands = Some(qs.clone().map(|(_, q_rand, _)| q_rand).collect());

        let f_polys: Vec<DensePolynomial<F>> = qs
            .map(|(q_poly, _, q_eval_set)| {
                let evaluation_domain: Vec<F> =
                    q_eval_set.keys().cloned().collect();

                let z_h = construct_vanishing(&evaluation_domain);

                // NOTE: We can omit r_poly since it's reminder in KATE division
                /*
                    p(x) - r(x) = 0 mod z_h(x)
                    p(x) = r(x) mod z_h(x)

                    so: p(x) / z_h(x) = q(x) + r(x)
                    => q(x) * r(x) = p(x) - r(x) which is exactly what we want

                */

                &q_poly / &z_h
            })
            .collect();

        let x2_powers: Vec<F> = successors(Some(F::one()), |x2_i| {
            Some(*x2_i * verifier_first_msg.x2)
        })
        .take(f_polys.len())
        .collect();

        let mut f_agg_poly = DensePolynomial::zero();
        for (i, f_i) in f_polys.iter().enumerate() {
            f_agg_poly += &(f_i * x2_powers[i])
        }

        // f is blinded with degree 1
        let f_agg_poly = LabeledPolynomial::new(
            "f_aggregated".to_string(),
            f_agg_poly,
            None,
            Some(1), // we open in x3, so we blind once
        );

        state.f_poly = Some(f_agg_poly.clone());
        Ok((f_agg_poly, state))
    }

    pub fn prover_second_round<'a, PC: HomomorphicCommitment<F>>(
        state: &'a ProverState<'a, F, PC>,
        verifier_second_msg: &VerifierSecondMsg<F>,
    ) -> Result<Vec<F>, PIOPError> {
        let q_polys =
            state.q_polys.as_ref().expect("Q polys should be in state");
        let q_evals = q_polys
            .iter()
            .map(|q_i| q_i.polynomial().evaluate(&verifier_second_msg.x3))
            .collect();
        Ok(q_evals)
    }

    pub fn prover_third_round<'a, PC: HomomorphicCommitment<F>>(
        state: &'a ProverState<'a, F, PC>,
        verifier_third_msg: &VerifierThirdMsg<F>,
        f_agg_poly_rand: &PC::Randomness,
    ) -> Result<
        (LabeledPolynomial<F, DensePolynomial<F>>, PC::Randomness),
        PIOPError,
    > {
        let q_polys =
            state.q_polys.as_ref().expect("Q polys should be in state");

        let q_rands =
            state.q_rands.as_ref().expect("Q rands should be in state");

        let f_poly = state.f_poly.as_ref().expect("F poly is not in the state");

        let x4_powers: Vec<F> =
            successors(Some(verifier_third_msg.x4), |x4_i| {
                Some(*x4_i * verifier_third_msg.x4)
            })
            .take(q_polys.len())
            .collect();

        let mut final_poly = f_poly.polynomial().clone();
        let mut final_poly_rand = f_agg_poly_rand.clone();
        for (i, (q_poly, q_rand)) in
            q_polys.iter().zip(q_rands.iter()).enumerate()
        {
            final_poly += &(q_poly.polynomial() * x4_powers[i]);
            final_poly_rand = PC::add_rands(
                &final_poly_rand,
                &PC::scale_rand(q_rand, x4_powers[i]),
            );
        }

        let final_poly = LabeledPolynomial::new(
            "final_poly".to_string(),
            final_poly,
            None,
            None,
        ); // Hiding will be derived with homomorphic property of randomness
        Ok((final_poly, final_poly_rand))
    }
}
