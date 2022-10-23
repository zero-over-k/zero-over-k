use std::collections::{BTreeMap, BTreeSet};

use ark_ff::PrimeField;
use ark_poly::{
    univariate::DensePolynomial, EvaluationDomain, GeneralEvaluationDomain,
    Polynomial, UVPolynomial,
};
use ark_poly_commit::{LabeledCommitment, LabeledPolynomial};

use crate::commitment::HomomorphicCommitment;

use super::{
    rotation::Rotation,
    traits::{
        CommittedOracle, ConcreteOracle, FixedOracle, Instantiable,
        QuerySetProvider,
    },
};

pub struct FixedProverOracle<F: PrimeField> {
    pub(crate) label: String,
    pub(crate) poly: DensePolynomial<F>,
    pub(crate) evals: Vec<F>,
    pub(crate) evals_at_coset_of_extended_domain: Option<Vec<F>>,
    pub(crate) queried_rotations: BTreeSet<Rotation>,
    // pub(crate) evals_at_challenges: BTreeMap<F, F>,
    // pub(crate) commitment: Option<PC::Commitment>,
}

impl<F: PrimeField> FixedProverOracle<F> {
    pub fn from_evals_and_domains(
        label: String,
        evals: &Vec<F>,
        domain: &GeneralEvaluationDomain<F>,
        extended_coset_domain: &GeneralEvaluationDomain<F>,
    ) -> Self {
        let poly =
            DensePolynomial::from_coefficients_slice(&domain.ifft(evals));
        Self {
            label: label.clone(),
            evals: evals.clone(),
            evals_at_coset_of_extended_domain: Some(
                extended_coset_domain.coset_fft(&poly),
            ),
            poly: poly,
            queried_rotations: BTreeSet::default(),
        }
    }
}

impl<F: PrimeField> FixedOracle<F> for FixedProverOracle<F> {}

impl<F: PrimeField> Clone for FixedProverOracle<F> {
    fn clone(&self) -> Self {
        Self {
            label: self.label.clone(),
            poly: self.poly.clone(),
            evals_at_coset_of_extended_domain: self
                .evals_at_coset_of_extended_domain
                .clone(),
            evals: self.evals.clone(),
            queried_rotations: self.queried_rotations.clone(),
            // evals_at_challenges: self.evals_at_challenges.clone(),
            // commitment: self.commitment.clone(),
        }
    }
}

// impl<F: PrimeField> FixedProverOracle<F> {
//     pub fn register_eval_at_challenge(&mut self, challenge: F, eval: F) {
//         let _ = self.evals_at_challenges.insert(challenge, eval);
//     }
// }

impl<F: PrimeField> ConcreteOracle<F> for FixedProverOracle<F> {
    fn register_rotation(&mut self, rotation: Rotation) {
        self.queried_rotations.insert(rotation);
    }

    fn get_degree(&self, domain_size: usize) -> usize {
        domain_size - 1
    }

    fn query(&self, challenge: &F) -> F {
        self.poly.evaluate(&challenge)
    }

    fn get_label(&self) -> String {
        self.label.clone()
    }

    fn get_queried_rotations(&self) -> &BTreeSet<Rotation> {
        &self.queried_rotations
    }
}

impl<F: PrimeField> Instantiable<F> for FixedProverOracle<F> {
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

    fn evals(&self) -> &Vec<F> {
        &self.evals
    }

    fn get_extended_coset_evals(&self) -> &Vec<F> {
        match &self.evals_at_coset_of_extended_domain {
            Some(evals) => evals,
            None => panic!("Extended coset evals for oracle with label {} of type fixed are not provided", self.label),
        }
    }
}

// impl<F: PrimeField> CommittedOracle<F, PC>
//     for FixedProverOracle<F>
// {
//     fn register_commitment(&mut self, c: <PC>::Commitment) {
//         self.commitment = Some(c);
//     }

//     fn get_commitment(&self) -> &<PC>::Commitment {
//         match &self.commitment {
//             Some(c) => c,
//             None => panic!("Commitment missing"),
//         }
//     }
// }

impl<F: PrimeField> QuerySetProvider<F> for FixedProverOracle<F> {}

pub struct FixedVerifierOracle<F: PrimeField, PC: HomomorphicCommitment<F>> {
    pub(crate) label: String,
    pub(crate) queried_rotations: BTreeSet<Rotation>,
    pub(crate) evals_at_challenges: BTreeMap<F, F>,
    pub(crate) commitment: Option<PC::Commitment>,
}

impl<F: PrimeField, PC: HomomorphicCommitment<F>> Clone
    for FixedVerifierOracle<F, PC>
{
    fn clone(&self) -> Self {
        Self {
            label: self.label.clone(),
            queried_rotations: self.queried_rotations.clone(),
            evals_at_challenges: self.evals_at_challenges.clone(),
            commitment: self.commitment.clone(),
        }
    }
}

impl<F: PrimeField, PC: HomomorphicCommitment<F>> FixedVerifierOracle<F, PC> {
    pub fn from_labeled_commitment(
        c: &LabeledCommitment<PC::Commitment>,
    ) -> Self {
        Self {
            label: c.label().clone(),
            queried_rotations: BTreeSet::default(),
            evals_at_challenges: BTreeMap::default(),
            commitment: Some(c.commitment().clone()),
        }
    }
    pub fn register_eval_at_challenge(&mut self, challenge: F, eval: F) {
        let _ = self.evals_at_challenges.insert(challenge, eval);
    }
}

impl<F: PrimeField, PC: HomomorphicCommitment<F>> FixedOracle<F>
    for FixedVerifierOracle<F, PC>
{
}

impl<F: PrimeField, PC: HomomorphicCommitment<F>> ConcreteOracle<F>
    for FixedVerifierOracle<F, PC>
{
    fn register_rotation(&mut self, rotation: Rotation) {
        self.queried_rotations.insert(rotation);
    }

    fn get_degree(&self, domain_size: usize) -> usize {
        domain_size - 1
    }

    fn query(&self, challenge: &F) -> F {
        match self.evals_at_challenges.get(&challenge) {
            Some(eval) => *eval,
            None => panic!(
                "No eval at challenge: {} of oracle {} with type witness",
                challenge, self.label
            ),
        }
    }

    fn get_label(&self) -> String {
        self.label.clone()
    }

    fn get_queried_rotations(&self) -> &BTreeSet<Rotation> {
        &self.queried_rotations
    }
}

impl<F: PrimeField, PC: HomomorphicCommitment<F>> CommittedOracle<F, PC>
    for FixedVerifierOracle<F, PC>
{
    fn register_commitment(&mut self, c: <PC>::Commitment) {
        self.commitment = Some(c);
    }

    fn get_commitment(&self) -> &<PC>::Commitment {
        match &self.commitment {
            Some(c) => c,
            None => panic!("Commitment for oracle {} not provided of type fixed", self.label),
        }
    }
}

impl<F: PrimeField, PC: HomomorphicCommitment<F>> QuerySetProvider<F>
    for FixedVerifierOracle<F, PC>
{
}
