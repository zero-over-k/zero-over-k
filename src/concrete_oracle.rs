use std::collections::{BTreeMap, BTreeSet};

use crate::vo::query::{Rotation, Sign};
use ark_ff::{Field, PrimeField};
use ark_poly::{
    univariate::DensePolynomial, EvaluationDomain, GeneralEvaluationDomain,
    Polynomial, UVPolynomial,
};

use ark_poly_commit::{LabeledPolynomial, PolynomialCommitment, QuerySet};
use ark_std::rand::Rng;

pub trait QuerySetProvider<F: PrimeField> {
    fn get_query_set(
        &self,
        opening_challenge_label: &str,
        opening_challenge: F,
        omegas: &Vec<F>,
    ) -> QuerySet<F>;
}

// TODO: add shared functionalities in trait
pub trait ConcreteOracle {}

#[derive(PartialEq, PartialOrd, Eq, Ord, Clone)]
pub enum OracleType {
    Witness,
    Instance,
}

// Note: We keep masking as flexible even when concrete oracle is of type witness
// In halo2 for example, wires are being masked with randomizing last m rows

/// Concrete oracle definition
#[derive(Clone)]
pub struct InstantiableConcreteOracle<F: PrimeField> {
    pub(crate) label: String,
    pub(crate) poly: DensePolynomial<F>,
    pub(crate) evals_at_coset_of_extended_domain: Option<Vec<F>>,
    pub(crate) oracle_type: OracleType,
    pub(crate) queried_rotations: BTreeSet<Rotation>,
    pub(crate) should_mask: bool,
}

impl<F: PrimeField> InstantiableConcreteOracle<F> {
    pub fn mask<R: Rng>(
        &mut self,
        vanishing_polynomial: &DensePolynomial<F>,
        rng: &mut R,
    ) {
        if !self.should_mask {
            return;
        }

        let masking = DensePolynomial::rand(self.queried_rotations.len(), rng);
        self.poly += &(vanishing_polynomial * &masking);
    }

    pub fn register_rotation(&mut self, rotation: Rotation) {
        self.queried_rotations.insert(rotation);
    }

    pub fn compute_extended_evals(
        &mut self,
        extended_domain: GeneralEvaluationDomain<F>,
    ) {
        self.evals_at_coset_of_extended_domain =
            Some(extended_domain.coset_fft(&self.poly));
    }

    pub fn get_degree(&self) -> usize {
        self.poly.degree()
    }

    pub fn query_at_challenge(&self, challenge: &F) -> F {
        self.poly.evaluate(challenge)
    }

    pub fn query_at_rotated_root_of_extended_domain(
        &self,
        original_domain_size: usize,
        rotation: Rotation,
        omega_i: usize,
    ) -> F {
        match &self.evals_at_coset_of_extended_domain {
            Some(evals) => {
                if rotation.degree == 0 {
                    return evals[omega_i];
                }
                let extended_domain_size = evals.len();
                let scaling_ratio = extended_domain_size / original_domain_size;
                let eval = match &rotation.sign {
                    Sign::Plus => {
                        evals[(omega_i + rotation.degree * scaling_ratio)
                            % extended_domain_size]
                    }
                    // TODO: test negative rotations
                    Sign::Minus => {
                        let index = omega_i as i64
                            - (rotation.degree * scaling_ratio) as i64;
                        if index >= 0 {
                            evals[index as usize]
                        } else {
                            let move_from_end =
                                (rotation.degree * scaling_ratio - omega_i)
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

    pub fn to_labeled(&self) -> LabeledPolynomial<F, DensePolynomial<F>> {
        // for now keep degree bound and hiding bound to None
        LabeledPolynomial::new(
            self.label.clone(),
            self.poly.clone(),
            None,
            None,
        )
    }
}

impl<F: PrimeField> QuerySetProvider<F> for &InstantiableConcreteOracle<F> {
    fn get_query_set(
        &self,
        opening_challenge_label: &str,
        opening_challenge: F,
        omegas: &Vec<F>,
    ) -> QuerySet<F> {
        let mut query_set = QuerySet::new();
        for rotation in &self.queried_rotations {
            let point_info = rotation.get_point_info(
                opening_challenge_label,
                opening_challenge,
                omegas,
            );
            query_set.insert((self.label.clone(), point_info));
        }

        query_set
    }
}

pub struct CommittedConcreteOracle<
    F: PrimeField,
    PC: PolynomialCommitment<F, DensePolynomial<F>>,
> {
    pub(crate) label: String,
    pub(crate) queried_rotations: BTreeSet<Rotation>,
    pub(crate) should_mask: bool,
    pub(crate) evals_at_challenges: BTreeMap<F, F>,
    pub(crate) commitment: Option<PC::Commitment>,
}

impl<F: PrimeField, PC: PolynomialCommitment<F, DensePolynomial<F>>> Clone
    for CommittedConcreteOracle<F, PC>
{
    fn clone(&self) -> Self {
        Self {
            label: self.label.clone(),
            queried_rotations: self.queried_rotations.clone(),
            should_mask: self.should_mask.clone(),
            evals_at_challenges: self.evals_at_challenges.clone(),
            commitment: self.commitment.clone(),
        }
    }
}

impl<F: PrimeField, PC: PolynomialCommitment<F, DensePolynomial<F>>>
    CommittedConcreteOracle<F, PC>
{
    pub fn new(label: String, should_mask: bool) -> Self {
        Self {
            label,
            should_mask,
            queried_rotations: BTreeSet::new(),
            evals_at_challenges: BTreeMap::new(),
            commitment: None,
        }
    }

    pub fn register_commitment(&mut self, c: PC::Commitment) {
        self.commitment = Some(c)
    }

    pub fn register_rotation(&mut self, rotation: Rotation) {
        self.queried_rotations.insert(rotation);
    }

    pub fn register_eval_at_challenge(&mut self, challenge: F, eval: F) {
        let prev_eval = self.evals_at_challenges.insert(challenge, eval);
        if !prev_eval.is_none() {
            panic!("Same eval already registered for challenge {}", challenge);
        }
    }

    pub fn get_degree(&self, domain_size: usize) -> usize {
        if self.should_mask {
            domain_size + self.queried_rotations.len()
        } else {
            domain_size - 1
        }
    }

    pub fn get_commitment(&self) -> &PC::Commitment {
        match &self.commitment {
            Some(c) => &c,
            None => panic!("Commitment not assigned for {} oracle", self.label),
        }
    }

    pub fn query_at_challenge(&self, challenge: &F) -> F {
        match self.evals_at_challenges.get(&challenge) {
            Some(eval) => *eval,
            None => panic!(
                "No eval at challenge: {} of oracle {}",
                challenge, self.label
            ),
        }
    }

    pub fn get_queried_rotations(&self) -> &BTreeSet<Rotation> {
        &self.queried_rotations
    }
}

impl<F: PrimeField, PC: PolynomialCommitment<F, DensePolynomial<F>>>
    QuerySetProvider<F> for &CommittedConcreteOracle<F, PC>
{
    fn get_query_set(
        &self,
        opening_challenge_label: &str,
        opening_challenge: F,
        omegas: &Vec<F>,
    ) -> QuerySet<F> {
        let mut query_set = QuerySet::new();
        for rotation in &self.queried_rotations {
            let point_info = rotation.get_point_info(
                opening_challenge_label,
                opening_challenge,
                omegas,
            );
            query_set.insert((self.label.clone(), point_info));
        }

        query_set
    }
}
