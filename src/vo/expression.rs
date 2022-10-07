// All credits to Halo2 devs for inspiration!

use std::{
    cmp::max,
    ops::{Add, Mul, Neg, Sub},
};

use super::{
    query::{InstanceQuery, WitnessQuery},
};
use ark_ff::PrimeField;

#[derive(Clone)]
pub enum Expression<F> {
    Constant(F),
    Instance(InstanceQuery),
    Witness(WitnessQuery),
    Negated(Box<Expression<F>>),
    Sum(Box<Expression<F>>, Box<Expression<F>>),
    Product(Box<Expression<F>>, Box<Expression<F>>),
    Scaled(Box<Expression<F>>, F),
}

impl<F: PrimeField> Expression<F> {
    /// Evaluate expression given generic closures that are provided
    /// When proving evals_at_coset_of_extended_domain can be queried
    /// and when verifying openings and challenges can be used
    #[allow(clippy::too_many_arguments)]
    pub fn evaluate<T>(
        &self,
        constant_fn: &impl Fn(F) -> T,
        wtns_fn: &impl Fn(&WitnessQuery) -> T,
        instance_fn: &impl Fn(&InstanceQuery) -> T,
        negated_fn: &impl Fn(T) -> T,
        sum_fn: &impl Fn(T, T) -> T,
        product_fn: &impl Fn(T, T) -> T,
        scaled_fn: &impl Fn(T, F) -> T,
    ) -> T {
        match self {
            Expression::Constant(scalar) => constant_fn(*scalar),
            Expression::Witness(query) => wtns_fn(query),
            Expression::Instance(query) => instance_fn(query),
            Expression::Negated(a) => {
                let a = a.evaluate(
                    constant_fn,
                    wtns_fn,
                    instance_fn,
                    negated_fn,
                    sum_fn,
                    product_fn,
                    scaled_fn,
                );
                negated_fn(a)
            }
            Expression::Sum(a, b) => {
                let a = a.evaluate(
                    constant_fn,
                    wtns_fn,
                    instance_fn,
                    negated_fn,
                    sum_fn,
                    product_fn,
                    scaled_fn,
                );
                let b = b.evaluate(
                    constant_fn,
                    wtns_fn,
                    instance_fn,
                    negated_fn,
                    sum_fn,
                    product_fn,
                    scaled_fn,
                );
                sum_fn(a, b)
            }
            Expression::Product(a, b) => {
                let a = a.evaluate(
                    constant_fn,
                    wtns_fn,
                    instance_fn,
                    negated_fn,
                    sum_fn,
                    product_fn,
                    scaled_fn,
                );
                let b = b.evaluate(
                    constant_fn,
                    wtns_fn,
                    instance_fn,
                    negated_fn,
                    sum_fn,
                    product_fn,
                    scaled_fn,
                );
                product_fn(a, b)
            }
            Expression::Scaled(a, f) => {
                let a = a.evaluate(
                    constant_fn,
                    wtns_fn,
                    instance_fn,
                    negated_fn,
                    sum_fn,
                    product_fn,
                    scaled_fn,
                );
                scaled_fn(a, *f)
            }
        }
    }
    /// Compute the degree of this polynomial
    pub fn degree(
        &self,
        wtns_fn: &impl Fn(&WitnessQuery) -> usize,
        instance_fn: &impl Fn(&InstanceQuery) -> usize,
    ) -> usize {
        match self {
            Expression::Constant(_) => 0,
            Expression::Witness(query) => wtns_fn(query),
            Expression::Instance(query) => instance_fn(query),
            Expression::Negated(poly) => poly.degree(wtns_fn, instance_fn),
            Expression::Sum(a, b) => max(
                a.degree(wtns_fn, instance_fn),
                b.degree(wtns_fn, instance_fn),
            ),
            Expression::Product(a, b) => {
                a.degree(wtns_fn, instance_fn) + b.degree(wtns_fn, instance_fn)
            }
            Expression::Scaled(poly, _) => poly.degree(wtns_fn, instance_fn),
        }
    }
}

impl<F: PrimeField> Neg for Expression<F> {
    type Output = Expression<F>;
    fn neg(self) -> Self::Output {
        Expression::Negated(Box::new(self))
    }
}

impl<F: PrimeField> Add for Expression<F> {
    type Output = Expression<F>;
    fn add(self, rhs: Expression<F>) -> Expression<F> {
        Expression::Sum(Box::new(self), Box::new(rhs))
    }
}

impl<F: PrimeField> Sub for Expression<F> {
    type Output = Expression<F>;
    fn sub(self, rhs: Expression<F>) -> Expression<F> {
        Expression::Sum(Box::new(self), Box::new(-rhs))
    }
}

impl<F: PrimeField> Mul for Expression<F> {
    type Output = Expression<F>;
    fn mul(self, rhs: Expression<F>) -> Expression<F> {
        Expression::Product(Box::new(self), Box::new(rhs))
    }
}

impl<F: PrimeField> Mul<F> for Expression<F> {
    type Output = Expression<F>;
    fn mul(self, rhs: F) -> Expression<F> {
        Expression::Scaled(Box::new(self), rhs)
    }
}

impl<F: PrimeField> From<WitnessQuery> for Expression<F> {
    fn from(query: WitnessQuery) -> Self {
        Self::Witness(query)
    }
}

impl<F: PrimeField> From<InstanceQuery> for Expression<F> {
    fn from(query: InstanceQuery) -> Self {
        Self::Instance(query)
    }
}