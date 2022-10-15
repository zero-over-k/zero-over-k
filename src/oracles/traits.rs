use std::collections::BTreeSet;

use ark_ff::{FftField, PrimeField};
use ark_poly::{univariate::DensePolynomial, GeneralEvaluationDomain};
use ark_poly_commit::{LabeledPolynomial, QuerySet};

use crate::commitment::HomomorphicCommitment;

use super::{query::QueryContext, rotation::Rotation};

pub trait ConcreteOracle<F: FftField> {
    fn get_label(&self) -> String;
    fn get_degree(&self, domain_size: usize) -> usize;
    fn get_queried_rotations(&self) -> &BTreeSet<Rotation>;
    fn register_rotation(&mut self, rotation: Rotation);
    fn query(&self, ctx: &QueryContext<F>) -> F;
}

pub trait Instantiable<F: FftField>: ConcreteOracle<F> {
    fn polynomial(&self) -> &DensePolynomial<F>;
    fn compute_extended_evals(
        &mut self,
        extended_domain: &GeneralEvaluationDomain<F>,
    );
    fn to_labeled(&self) -> LabeledPolynomial<F, DensePolynomial<F>>;
}

pub trait CommittedOracle<F: PrimeField, PC: HomomorphicCommitment<F>>:
    ConcreteOracle<F>
{
    fn register_commitment(&mut self, c: PC::Commitment);
    fn get_commitment(&self) -> &PC::Commitment;
}

pub trait WitnessOracle<F: PrimeField>: ConcreteOracle<F> {}

pub trait QuerySetProvider<F: PrimeField>: ConcreteOracle<F> {
    fn get_query_set(
        &self,
        opening_challenge_label: &str,
        opening_challenge: F,
        omegas: &Vec<F>,
    ) -> QuerySet<F>;
}
