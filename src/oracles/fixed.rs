use std::collections::{BTreeMap, BTreeSet};

use ark_ff::PrimeField;
use ark_poly::{
    univariate::DensePolynomial, EvaluationDomain, GeneralEvaluationDomain,
    Polynomial,
};
use ark_poly_commit::{LabeledPolynomial, QuerySet};

use crate::commitment::HomomorphicCommitment;

use super::{
    query::QueryContext,
    rotation::{Rotation, Sign},
    traits::{CommittedOracle, ConcreteOracle, Instantiable, QuerySetProvider},
};

pub struct FixedOracle<F: PrimeField, PC: HomomorphicCommitment<F>> {
    pub(crate) label: String,
    pub(crate) poly: DensePolynomial<F>,
    pub(crate) evals_at_coset_of_extended_domain: Option<Vec<F>>,
    pub(crate) queried_rotations: BTreeSet<Rotation>,
    pub(crate) evals_at_challenges: BTreeMap<F, F>,
    pub(crate) commitment: Option<PC::Commitment>,
}

impl<F: PrimeField, PC: HomomorphicCommitment<F>> Clone for FixedOracle<F, PC> {
    fn clone(&self) -> Self {
        Self {
            label: self.label.clone(),
            poly: self.poly.clone(),
            evals_at_coset_of_extended_domain: self
                .evals_at_coset_of_extended_domain
                .clone(),
            queried_rotations: self.queried_rotations.clone(),
            evals_at_challenges: self.evals_at_challenges.clone(),
            commitment: self.commitment.clone(),
        }
    }
}

//TODO: move this to committed trait
impl<F: PrimeField, PC: HomomorphicCommitment<F>> FixedOracle<F, PC> {
    pub fn register_eval_at_challenge(&mut self, challenge: F, eval: F) {
        let _ = self.evals_at_challenges.insert(challenge, eval);
        // if !prev_eval.is_none() {
        //     panic!("Same eval already registered for challenge {}", challenge);
        // }
    }
}

impl<F: PrimeField, PC: HomomorphicCommitment<F>> ConcreteOracle<F>
    for FixedOracle<F, PC>
{
    fn register_rotation(&mut self, rotation: Rotation) {
        self.queried_rotations.insert(rotation);
    }

    fn get_degree(&self, domain_size: usize) -> usize {
        domain_size - 1
    }

    fn query(&self, ctx: &QueryContext<F>) -> F {
        match ctx {
            QueryContext::Challenge(challenge) => {
                // TODO: when on verifier side we should keep poly to None and eval as Committed oracle
                // on verifier side we keep poly and evaluate normaly
                // match self.evals_at_challenges.get(&challenge) {
                //     Some(eval) => *eval,
                //     None => panic!(
                //         "No eval at challenge: {} of oracle {}",
                //         challenge, self.label
                //     ),
                // }
                self.poly.evaluate(&challenge)
            }
            QueryContext::ExtendedCoset(
                original_domain_size,
                rotation,
                omega_i,
            ) => {
                match &self.evals_at_coset_of_extended_domain {
                    Some(evals) => {
                        if rotation.degree == 0 {
                            return evals[*omega_i];
                        }
                        let extended_domain_size = evals.len();
                        let scaling_ratio =
                            extended_domain_size / original_domain_size;
                        let eval = match &rotation.sign {
                            Sign::Plus => {
                                evals[(omega_i
                                    + rotation.degree * scaling_ratio)
                                    % extended_domain_size]
                            }
                            // TODO: test negative rotations
                            Sign::Minus => {
                                let index = *omega_i as i64
                                    - (rotation.degree * scaling_ratio) as i64;
                                if index >= 0 {
                                    evals[index as usize]
                                } else {
                                    let move_from_end = (rotation.degree
                                        * scaling_ratio
                                        - omega_i)
                                        % extended_domain_size;
                                    evals[extended_domain_size - move_from_end]
                                }
                            }
                        };
                        return eval;
                    }
                    None => panic!("Evals not provided"),
                }
            }
        }
    }

    fn get_label(&self) -> String {
        self.label.clone()
    }

    fn get_queried_rotations(&self) -> &BTreeSet<Rotation> {
        &self.queried_rotations
    }
}

impl<F: PrimeField, PC: HomomorphicCommitment<F>> Instantiable<F>
    for FixedOracle<F, PC>
{
    fn compute_extended_evals(
        &mut self,
        extended_domain: &GeneralEvaluationDomain<F>,
    ) {
        self.evals_at_coset_of_extended_domain =
            Some(extended_domain.coset_fft(&self.poly));
    }

    fn to_labeled(&self) -> LabeledPolynomial<F, DensePolynomial<F>> {
        LabeledPolynomial::new(
            self.label.clone(),
            self.poly.clone(),
            None,
            None, // blinding is not required for public polynomials
        )
    }

    fn polynomial(&self) -> &DensePolynomial<F> {
        &self.poly
    }
}

impl<F: PrimeField, PC: HomomorphicCommitment<F>> CommittedOracle<F, PC>
    for FixedOracle<F, PC>
{
    fn register_commitment(&mut self, c: <PC>::Commitment) {
        self.commitment = Some(c);
    }

    fn get_commitment(&self) -> &<PC>::Commitment {
        match &self.commitment {
            Some(c) => c,
            None => panic!("Commitment missing"),
        }
    }
}

impl<F: PrimeField, PC: HomomorphicCommitment<F>> QuerySetProvider<F>
    for FixedOracle<F, PC>
{
    fn get_query_set(
        &self,
        opening_challenge_label: &str,
        opening_challenge: F,
        omegas: &Vec<F>,
    ) -> QuerySet<F> {
        let mut query_set = QuerySet::new();
        for rotation in self.get_queried_rotations() {
            let point_info = rotation.get_point_info(
                opening_challenge_label,
                opening_challenge,
                omegas,
            );
            query_set.insert((self.get_label(), point_info));
        }

        query_set
    }
}
