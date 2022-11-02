use std::collections::{BTreeMap, BTreeSet};

use ark_ff::PrimeField;
use ark_poly::{
    univariate::DensePolynomial, EvaluationDomain, GeneralEvaluationDomain,
    Polynomial,
};
use ark_poly_commit::LabeledPolynomial;

use crate::commitment::HomomorphicCommitment;

use super::{
    rotation::Rotation,
    traits::{
        CommittedOracle, ConcreteOracle, Instantiable, QuerySetProvider,
        WitnessOracle,
    },
};

#[derive(Clone)]
pub struct WitnessProverOracle<F: PrimeField> {
    pub(crate) label: String,
    pub(crate) poly: DensePolynomial<F>,
    pub(crate) evals: Vec<F>,
    pub(crate) evals_at_coset_of_extended_domain: Option<Vec<F>>,
    pub(crate) queried_rotations: BTreeSet<Rotation>,
    pub(crate) should_permute: bool,
}

impl<F: PrimeField> WitnessProverOracle<F> {
    /// Creates a new WitnessProverOracle
    pub(crate) fn new(
        label: impl Into<String>,
        poly: DensePolynomial<F>,
        evals: &[F],
        should_permute: bool,
    ) -> Self {
        Self {
            label: label.into(),
            poly,
            evals: evals.to_vec(),
            evals_at_coset_of_extended_domain: None,
            queried_rotations: BTreeSet::new(),
            should_permute,
        }
    }
}

impl<F: PrimeField> WitnessOracle<F> for WitnessProverOracle<F> {
    fn should_include_in_copy(&self) -> bool {
        self.should_permute
    }
}

impl<F: PrimeField> ConcreteOracle<F> for WitnessProverOracle<F> {
    fn register_rotation(&mut self, rotation: Rotation) {
        self.queried_rotations.insert(rotation);
    }

    fn query(&self, challenge: &F) -> F {
        self.poly.evaluate(challenge)
    }

    fn get_label(&self) -> String {
        self.label.clone()
    }

    fn get_queried_rotations(&self) -> &BTreeSet<Rotation> {
        &self.queried_rotations
    }
}

impl<F: PrimeField> Instantiable<F> for WitnessProverOracle<F> {
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
            Some(1), // blind for opening in x3 in multiproof
        )
    }

    fn polynomial(&self) -> &DensePolynomial<F> {
        &self.poly
    }

    fn get_extended_coset_evals(&self) -> &Vec<F> {
        match &self.evals_at_coset_of_extended_domain {
            Some(evals) => evals,
            None => panic!("Extended coset evals for oracle with label {} of type witness are not provided", self.label),
        }
    }

    fn evals(&self) -> &Vec<F> {
        &self.evals
    }
}

impl<F: PrimeField> QuerySetProvider<F> for WitnessProverOracle<F> {}

pub struct WitnessVerifierOracle<F: PrimeField, PC: HomomorphicCommitment<F>> {
    pub(crate) label: String,
    pub(crate) queried_rotations: BTreeSet<Rotation>,
    pub(crate) evals_at_challenges: BTreeMap<F, F>,
    pub(crate) commitment: Option<PC::Commitment>,
    pub(crate) should_permute: bool,
}

impl<F: PrimeField, PC: HomomorphicCommitment<F>> WitnessVerifierOracle<F, PC> {
    /// Create a new WitnessVerifierOracle
    pub(crate) fn new(label: impl Into<String>, should_permute: bool) -> Self {
        Self {
            label: label.into(),
            evals_at_challenges: BTreeMap::new(),
            queried_rotations: BTreeSet::new(),
            commitment: None,
            should_permute,
        }
    }
}

impl<F: PrimeField, PC: HomomorphicCommitment<F>> WitnessVerifierOracle<F, PC> {
    pub fn register_eval_at_challenge(&mut self, challenge: F, eval: F) {
        let _ = self.evals_at_challenges.insert(challenge, eval);
    }
}

impl<F: PrimeField, PC: HomomorphicCommitment<F>> WitnessOracle<F>
    for WitnessVerifierOracle<F, PC>
{
    fn should_include_in_copy(&self) -> bool {
        self.should_permute
    }
}

impl<F: PrimeField, PC: HomomorphicCommitment<F>> Clone
    for WitnessVerifierOracle<F, PC>
{
    fn clone(&self) -> Self {
        Self {
            label: self.label.clone(),
            queried_rotations: self.queried_rotations.clone(),
            evals_at_challenges: self.evals_at_challenges.clone(),
            commitment: self.commitment.clone(),
            should_permute: self.should_permute.clone(),
        }
    }
}

impl<F: PrimeField, PC: HomomorphicCommitment<F>> ConcreteOracle<F>
    for WitnessVerifierOracle<F, PC>
{
    fn register_rotation(&mut self, rotation: Rotation) {
        self.queried_rotations.insert(rotation);
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
    for WitnessVerifierOracle<F, PC>
{
    fn register_commitment(&mut self, c: <PC>::Commitment) {
        self.commitment = Some(c);
    }

    fn get_commitment(&self) -> &<PC>::Commitment {
        match &self.commitment {
            Some(c) => c,
            None => panic!("Commitment not provided"),
        }
    }
}

impl<F: PrimeField, PC: HomomorphicCommitment<F>> QuerySetProvider<F>
    for WitnessVerifierOracle<F, PC>
{
}
