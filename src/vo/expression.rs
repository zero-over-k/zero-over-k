use crate::oracles::query::OracleQuery;
use ark_ff::PrimeField;
use std::ops::{Add, Mul, Neg, Sub};

#[derive(Clone)]
pub enum Expression<F> {
    Constant(F),
    Oracle(OracleQuery),
    Negated(Box<Expression<F>>),
    Sum(Box<Expression<F>>, Box<Expression<F>>),
    Product(Box<Expression<F>>, Box<Expression<F>>),
    Scaled(Box<Expression<F>>, F),
}

impl<F: PrimeField> Expression<F> {
    pub fn degree(&self, oracle_fn: &impl Fn(&OracleQuery) -> usize) -> usize {
        match self {
            Expression::Constant(_) => 0,
            Expression::Oracle(query) => oracle_fn(query),
            Expression::Negated(expr) => expr.degree(oracle_fn),
            Expression::Sum(lsh_expr, rhs_expr) => std::cmp::max(
                lsh_expr.degree(oracle_fn),
                rhs_expr.degree(oracle_fn),
            ),
            Expression::Product(lsh_expr, rhs_expr) => {
                lsh_expr.degree(oracle_fn) + rhs_expr.degree(oracle_fn)
            }
            Expression::Scaled(expr, _) => expr.degree(oracle_fn),
        }
    }

    /// Evaluate expression given generic closures that are provided
    /// When proving evals_at_coset_of_extended_domain can be queried
    /// and when verifying openings and challenges can be used
    #[allow(clippy::too_many_arguments)]
    pub fn evaluate<T>(
        &self,
        constant_fn: &impl Fn(F) -> T,
        oracle_fn: &impl Fn(&OracleQuery) -> T,
        negated_fn: &impl Fn(T) -> T,
        sum_fn: &impl Fn(T, T) -> T,
        product_fn: &impl Fn(T, T) -> T,
        scaled_fn: &impl Fn(T, F) -> T,
    ) -> T {
        match self {
            Expression::Constant(scalar) => constant_fn(*scalar),
            Expression::Oracle(query) => oracle_fn(query),
            Expression::Negated(a) => {
                let a = a.evaluate(
                    constant_fn,
                    oracle_fn,
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
                    oracle_fn,
                    negated_fn,
                    sum_fn,
                    product_fn,
                    scaled_fn,
                );
                let b = b.evaluate(
                    constant_fn,
                    oracle_fn,
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
                    oracle_fn,
                    negated_fn,
                    sum_fn,
                    product_fn,
                    scaled_fn,
                );
                let b = b.evaluate(
                    constant_fn,
                    oracle_fn,
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
                    oracle_fn,
                    negated_fn,
                    sum_fn,
                    product_fn,
                    scaled_fn,
                );
                scaled_fn(a, *f)
            }
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

impl<F: PrimeField> From<OracleQuery> for Expression<F> {
    fn from(query: OracleQuery) -> Self {
        Self::Oracle(query)
    }
}
