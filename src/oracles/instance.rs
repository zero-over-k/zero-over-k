use std::collections::BTreeSet;

use crate::piop::error::Error;
use ark_ff::PrimeField;
use ark_poly::{
    univariate::DensePolynomial, EvaluationDomain, GeneralEvaluationDomain,
    Polynomial,
};
use ark_poly_commit::LabeledPolynomial;

use super::{
    rotation::Rotation,
    traits::{ConcreteOracle, InstanceOracle, Instantiable},
};

#[derive(Clone)]
pub struct InstanceProverOracle<F: PrimeField> {
    pub(crate) label: String,
    pub(crate) poly: DensePolynomial<F>,
    pub(crate) evals: Vec<F>,
    pub(crate) evals_at_coset_of_extended_domain: Option<Vec<F>>,
    pub(crate) queried_rotations: BTreeSet<Rotation>,
}

impl<F: PrimeField> InstanceProverOracle<F> {
    /// Creates a new InstanceProverOracle
    pub(crate) fn new(
        label: impl Into<String>,
        poly: DensePolynomial<F>,
        evals: &[F],
    ) -> Self {
        Self {
            label: label.into(),
            poly,
            evals: evals.to_vec(),
            evals_at_coset_of_extended_domain: None,
            queried_rotations: BTreeSet::new(),
        }
    }
}

impl<F: PrimeField> InstanceOracle<F> for InstanceProverOracle<F> {}

impl<F: PrimeField> ConcreteOracle<F> for InstanceProverOracle<F> {
    fn register_rotation(&mut self, rotation: Rotation) {
        self.queried_rotations.insert(rotation);
    }

    fn query(&self, challenge: &F) -> Result<F, Error> {
        Ok(self.poly.evaluate(challenge))
    }

    fn get_label(&self) -> String {
        self.label.clone()
    }

    fn get_queried_rotations(&self) -> &BTreeSet<Rotation> {
        &self.queried_rotations
    }
}

impl<F: PrimeField> Instantiable<F> for InstanceProverOracle<F> {
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
            None, // blinding is not required for instance polynomials
        )
    }

    fn polynomial(&self) -> &DensePolynomial<F> {
        &self.poly
    }

    fn get_extended_coset_evals(&self) -> &Vec<F> {
        match &self.evals_at_coset_of_extended_domain {
            Some(evals) => evals,
            None => panic!("Extended coset evals for oracle with label {} of type instance are not provided", self.label),
        }
    }

    fn evals(&self) -> &Vec<F> {
        &self.evals
    }
}

pub struct InstanceVerifierOracle<F: PrimeField> {
    pub(crate) label: String,
    pub(crate) poly: DensePolynomial<F>,
    pub(crate) evals: Vec<F>, // TODO enable evals with lagrange
    pub(crate) queried_rotations: BTreeSet<Rotation>,
}

impl<F: PrimeField> InstanceVerifierOracle<F> {
    /// Creates a new InstanceVerifierOracle
    pub(crate) fn new(
        label: impl Into<String>,
        poly: DensePolynomial<F>,
        evals: &[F],
    ) -> Self {
        Self {
            label: label.into(),
            poly,
            evals: evals.to_vec(),
            queried_rotations: BTreeSet::new(),
        }
    }
}

impl<F: PrimeField> InstanceOracle<F> for InstanceVerifierOracle<F> {}

impl<F: PrimeField> ConcreteOracle<F> for InstanceVerifierOracle<F> {
    fn register_rotation(&mut self, rotation: Rotation) {
        self.queried_rotations.insert(rotation);
    }

    fn query(&self, challenge: &F) -> Result<F, Error> {
        Ok(self.poly.evaluate(challenge))
    }

    fn get_label(&self) -> String {
        self.label.clone()
    }

    fn get_queried_rotations(&self) -> &BTreeSet<Rotation> {
        &self.queried_rotations
    }
}
