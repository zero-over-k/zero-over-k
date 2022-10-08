use std::collections::{BTreeMap, BTreeSet};
use std::iter::successors;

use ark_ff::{PrimeField, Zero};
use ark_poly::univariate::DensePolynomial;
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain, Polynomial};
use ark_poly_commit::LabeledPolynomial;

use crate::multiproof::poly::construct_vanishing;
use crate::{concrete_oracle::InstantiableConcreteOracle, vo::query::Rotation};

use super::{PIOPError, PIOP};
use super::verifier::{VerifierFirstMsg, VerifierSecondMsg, VerifierThirdMsg};

pub struct ProverState<'a, F: PrimeField> {
    oracles: &'a [InstantiableConcreteOracle<F>],
    opening_sets:
        BTreeMap<BTreeSet<Rotation>, Vec<&'a InstantiableConcreteOracle<F>>>,
    domain: GeneralEvaluationDomain<F>,
    q_polys: Option<Vec<LabeledPolynomial<F, DensePolynomial<F>>>>,
    f_poly: Option<LabeledPolynomial<F, DensePolynomial<F>>>
}

impl<F: PrimeField> PIOP<F> {
    // NOTE: Oracles are already masked
    pub fn init_prover<'a>(
        oracles: &'a [InstantiableConcreteOracle<F>],
        domain_size: usize,
    ) -> Result<ProverState<'a, F>, PIOPError> {
        let mut opening_sets = BTreeMap::<
            BTreeSet<Rotation>,
            Vec<&'a InstantiableConcreteOracle<F>>,
        >::new();

        for oracle in oracles.iter() {
            let oracles = opening_sets
                .entry(oracle.queried_rotations.clone())
                .or_insert(vec![]);
            oracles.push(oracle)
        }

        let domain = GeneralEvaluationDomain::<F>::new(domain_size).unwrap();

        let state = ProverState {
            oracles,
            opening_sets,
            domain,
            q_polys: None,
            f_poly: None,
        };

        Ok(state)
    }

    pub fn prover_first_round<'a>(
        mut state: ProverState<'a, F>,
        evaluation_challenge: F,
        verifier_first_msg: &VerifierFirstMsg<F>,
    ) -> Result<
        (
            LabeledPolynomial<F, DensePolynomial<F>>,
            ProverState<'a, F>,
        ),
        PIOPError,
    > {
        // Max number of oracles in one opening set are all oracles
        let x1_powers: Vec<F> = successors(Some(F::one()), |x1_i| {
            Some(*x1_i * verifier_first_msg.x1)
        })
        .take(state.oracles.len())
        .collect();

        let qs = state.opening_sets.iter().map(|(rotations, oracles)| {
            let mut q_i = DensePolynomial::zero();
            let mut q_i_evals_set = BTreeMap::<F, F>::new();

            for (i, &oracle) in oracles.iter().enumerate() {
                q_i = q_i + &oracle.poly * x1_powers[i];
            }

            let omegas: Vec<F> = state.domain.elements().collect();
            for rotation in rotations {
                let evaluation_point = rotation
                    .compute_evaluation_point(evaluation_challenge, &omegas);
                let mut evaluation = F::zero();
                for (i, &oracle) in oracles.iter().enumerate() {
                    evaluation += x1_powers[i]
                        * oracle.query_at_challenge(&evaluation_point);
                }

                let prev = q_i_evals_set.insert(evaluation_point, evaluation);
                if prev.is_some() {
                    panic!("Same evaluation point for different rotations")
                }
            }

            (q_i, q_i_evals_set)
        });

        state.q_polys = Some(
            qs.clone()
                .map(|(q_poly, _)| {
                    LabeledPolynomial::new(
                        "q_i".to_string(),
                        q_poly,
                        None,
                        None,
                    )
                })
                .collect(),
        );

        let f_polys: Vec<LabeledPolynomial<F, DensePolynomial<F>>> = qs
            .map(|(q_poly, q_eval_set)| {
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

                LabeledPolynomial::new(
                    "f_i".to_string(),
                    &q_poly / &z_h,
                    None,
                    None,
                )
            })
            .collect();

        let x2_powers: Vec<F> = successors(Some(F::one()), |x2_i| {
            Some(*x2_i * verifier_first_msg.x2)
        })
        .take(f_polys.len())
        .collect();

        let mut f_agg_poly = DensePolynomial::zero();
        for (i, f_i) in f_polys.iter().enumerate() {
            f_agg_poly += &(f_i.polynomial() * x2_powers[i])
        }

        // f is blinded with degree 1
        let f_agg_poly = LabeledPolynomial::new(
            "f_aggregated".to_string(),
            f_agg_poly,
            None,
            None, // don't forget to blind
        );

        state.f_poly = Some(f_agg_poly.clone());
        Ok((f_agg_poly, state))
    }

    pub fn prover_second_round<'a>(
        state: &'a ProverState<'a, F>,
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

    pub fn prover_third_round<'a>(
        state: &'a ProverState<'a, F>,
        verifier_third_msg: &VerifierThirdMsg<F>,
    ) -> Result<LabeledPolynomial<F, DensePolynomial<F>>, PIOPError> {
        let q_polys =
            state.q_polys.as_ref().expect("Q polys should be in state");

        let f_poly = state.f_poly.as_ref().expect("F poly is not in the state");

        let x4_powers: Vec<F> =
            successors(Some(verifier_third_msg.x4), |x4_i| {
                Some(*x4_i * verifier_third_msg.x4)
            })
            .take(q_polys.len())
            .collect();

        let mut final_poly = f_poly.polynomial().clone();
        for (i, q_poly) in q_polys.iter().enumerate() {
            final_poly += &(q_poly.polynomial() * x4_powers[i]);
        }

        let final_poly = LabeledPolynomial::new("final_poly".to_string(), final_poly, None, None);
        Ok(final_poly)
    }
}
