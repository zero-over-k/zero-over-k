use std::ops::{Add, Mul, Neg, Sub};

use ark_ff::{PrimeField, Zero};
use ark_poly::univariate::DensePolynomial;

use crate::{commitment::HomomorphicCommitment, concrete_oracle::OracleType};

use super::query::Rotation;

pub enum LinearisationType {
    Proving,
    Verifying,
}
#[derive(Clone)]
pub enum LinearisationQueryContext {
    AsEval,
    AsPoly,
}

#[derive(Clone)]
pub struct LinearisationOracleQuery {
    pub(crate) index: usize,
    pub(crate) rotation: Rotation,
    pub(crate) oracle_type: OracleType,
    pub(crate) ctx: LinearisationQueryContext,
}

#[derive(Clone)]
pub struct LinearisationInfo<F: PrimeField> {
    pub domain_size: usize,
    pub opening_challenge: F,
}

pub enum LinearisationQueryResponse<F: PrimeField, PC: HomomorphicCommitment<F>>
{
    Opening(F),
    Poly(DensePolynomial<F>),
    Commitment(PC::Commitment),
}

pub trait LinearisationQueriable<F: PrimeField, PC: HomomorphicCommitment<F>> {
    fn query_for_linearisation(
        &self,
        rotation: &Rotation,
        context: &LinearisationQueryContext,
        info: &LinearisationInfo<F>,
    ) -> LinearisationQueryResponse<F, PC>;
}

// We keep const part of linearisation poly separated to spare scalar multiplication for verifier
pub struct LinearisationPolyCommitment<
    F: PrimeField,
    PC: HomomorphicCommitment<F>,
> {
    pub comm: PC::Commitment,
    pub r0: F,
}

impl<F: PrimeField, PC: HomomorphicCommitment<F>>
    LinearisationPolyCommitment<F, PC>
{
    pub fn from_const(r0: F) -> Self {
        Self {
            comm: PC::zero_comm(),
            r0,
        }
    }

    pub fn from_commitment(c: PC::Commitment) -> Self {
        Self {
            comm: c,
            r0: F::zero(),
        }
    }

    pub fn is_const(&self) -> bool {
        PC::is_zero(&self.comm) && !self.r0.is_zero()
    }
}

impl<F: PrimeField, PC: HomomorphicCommitment<F>> Zero
    for LinearisationPolyCommitment<F, PC>
{
    fn zero() -> Self {
        Self {
            comm: PC::zero_comm(),
            r0: F::zero(),
        }
    }

    fn is_zero(&self) -> bool {
        PC::is_zero(&self.comm) && self.r0.is_zero()
    }
}

// TODO: Consider deriving Add, Neg, Mul for PC::Commitment

impl<F: PrimeField, PC: HomomorphicCommitment<F>> Neg
    for LinearisationPolyCommitment<F, PC>
{
    type Output = Self;
    fn neg(self) -> Self::Output {
        Self {
            comm: PC::neg_com(&self.comm),
            r0: -self.r0,
        }
    }
}

impl<F: PrimeField, PC: HomomorphicCommitment<F>> Add
    for LinearisationPolyCommitment<F, PC>
{
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        Self {
            comm: PC::add(&self.comm, &rhs.comm),
            r0: self.r0 + rhs.r0,
        }
    }
}

impl<F: PrimeField, PC: HomomorphicCommitment<F>> Sub
    for LinearisationPolyCommitment<F, PC>
{
    type Output = Self;
    fn sub(self, rhs: Self) -> Self::Output {
        Self {
            comm: PC::add(&self.comm, &PC::neg_com(&rhs.comm)),
            r0: self.r0 - rhs.r0,
        }
    }
}

impl<F: PrimeField, PC: HomomorphicCommitment<F>> Mul<F>
    for LinearisationPolyCommitment<F, PC>
{
    type Output = Self;
    fn mul(self, rhs: F) -> Self::Output {
        Self {
            comm: PC::scale_com(&self.comm, rhs),
            r0: self.r0 * rhs,
        }
    }
}
