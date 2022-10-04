use std::ops::Neg;

use ark_ff::PrimeField;
use ark_poly::univariate::DensePolynomial;
use ark_poly_commit::PolynomialCommitment;

use crate::{concrete_oracle::{DomainSize, OracleType}, commitment::HomomorphicCommitment};

use super::query::Rotation;

pub enum LinearisationType {
    Proving, 
    Verifying
}
#[derive(Clone)]
pub enum LinearisationQueryContext {
    AsEval,
    AsPoly
}

#[derive(Clone)]
pub struct LinearisationOracleQuery {
    pub(crate) index: usize,
    pub(crate) rotation: Rotation,
    pub(crate) oracle_type: OracleType, 
    pub(crate) ctx: LinearisationQueryContext
}

#[derive(Clone)]
pub struct LinearisationInfo<F: PrimeField> {
    pub domain_size: usize, 
    pub opening_challenge: F
}

// pub enum 

pub enum LinearisationQueryResponse<F: PrimeField, PC: HomomorphicCommitment<F>> {
    Opening(F),
    Poly(DensePolynomial<F>),
    Commitment(PC::Commitment)
}

pub trait LinearisationQueriable<F: PrimeField, PC: HomomorphicCommitment<F>> {
    fn query_for_linearisation(&self, rotation: &Rotation, context: &LinearisationQueryContext, info: &LinearisationInfo<F>) -> LinearisationQueryResponse<F, PC>;
}
