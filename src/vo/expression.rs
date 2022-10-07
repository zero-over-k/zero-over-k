use std::{
    cmp::max,
    ops::{Add, Mul, Neg, Sub},
};

use super::{
    linearisation::LinearisationOracleQuery,
    query::{InstanceQuery, WitnessQuery},
};
use ark_ff::PrimeField;
use ark_poly_commit::QuerySet;

#[derive(Clone)]
pub enum Expression<F> {
    Constant(F),
    Instance(InstanceQuery),
    Witness(WitnessQuery),
    Negated(Box<Expression<F>>),
    Sum(Box<Expression<F>>, Box<Expression<F>>),
    Product(Box<Expression<F>>, Box<Expression<F>>),
    Scaled(Box<Expression<F>>, F),

    Linearisation(LinearisationOracleQuery),
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

        linearisation_fn: &impl Fn(&LinearisationOracleQuery) -> T,
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
                    linearisation_fn,
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
                    linearisation_fn,
                );
                let b = b.evaluate(
                    constant_fn,
                    wtns_fn,
                    instance_fn,
                    negated_fn,
                    sum_fn,
                    product_fn,
                    scaled_fn,
                    linearisation_fn,
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
                    linearisation_fn,
                );
                let b = b.evaluate(
                    constant_fn,
                    wtns_fn,
                    instance_fn,
                    negated_fn,
                    sum_fn,
                    product_fn,
                    scaled_fn,
                    linearisation_fn,
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
                    linearisation_fn,
                );
                scaled_fn(a, *f)
            }
            Expression::Linearisation(query) => linearisation_fn(query),
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
            Expression::Linearisation(_) => panic!("skip degree for now"),
        }
    }

    /// Compute which oracles should be queried at which rotations
    pub fn compute_query_set(
        &self,
        wtns_fn: &impl Fn(&WitnessQuery) -> Vec<(String, (String, F))>,
    ) -> Vec<(String, (String, F))> {
        match self {
            Expression::Constant(_) => vec![],
            Expression::Witness(query) => wtns_fn(query),
            Expression::Instance(query) => vec![], // we don't commit&open to instance polys
            Expression::Negated(expression) => {
                expression.compute_query_set(wtns_fn)
            }
            Expression::Sum(a, b) => {
                let mut lhs = a.compute_query_set(wtns_fn);
                let rhs = b.compute_query_set(wtns_fn);
                lhs.extend(rhs);
                lhs
            }
            Expression::Product(a, b) => {
                let mut lhs = a.compute_query_set(wtns_fn);
                let rhs = b.compute_query_set(wtns_fn);
                lhs.extend(rhs);
                lhs
            }
            Expression::Scaled(exp, _) => exp.compute_query_set(wtns_fn),
            Expression::Linearisation(_) => panic!("Not allowed here"),
        }
    }

    pub fn compute_linearisation_query_set(
        &self,
        oracle_fn: &impl Fn(&LinearisationOracleQuery) -> Vec<(String, (String, F))>,
    ) -> Vec<(String, (String, F))> {
        match self {
            Expression::Constant(_) => vec![],
            Expression::Witness(_) => panic!("Not allowed"),
            Expression::Instance(_) => panic!("Not allowed"),
            Expression::Negated(expression) => {
                expression.compute_linearisation_query_set(oracle_fn)
            }
            Expression::Sum(a, b) => {
                let mut lhs = a.compute_linearisation_query_set(oracle_fn);
                let rhs = b.compute_linearisation_query_set(oracle_fn);
                lhs.extend(rhs);
                lhs
            }
            Expression::Product(a, b) => {
                let mut lhs = a.compute_linearisation_query_set(oracle_fn);
                let rhs = b.compute_linearisation_query_set(oracle_fn);
                lhs.extend(rhs);
                lhs
            }
            Expression::Scaled(exp, _) => {
                exp.compute_linearisation_query_set(oracle_fn)
            }
            Expression::Linearisation(query) => oracle_fn(query),
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

impl<F: PrimeField> From<LinearisationOracleQuery> for Expression<F> {
    fn from(query: LinearisationOracleQuery) -> Self {
        Self::Linearisation(query)
    }
}
