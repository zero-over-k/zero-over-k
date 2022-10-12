use std::ops::{Neg, Add, Mul, Sub};

use ark_ff::PrimeField;

use crate::oracles::query::OracleQuery;

#[derive(Clone)]
pub enum NewExpression<F> {
    Constant(F),
    Oracle(OracleQuery),
    Negated(Box<NewExpression<F>>),
    Sum(Box<NewExpression<F>>, Box<NewExpression<F>>),
    Product(Box<NewExpression<F>>, Box<NewExpression<F>>),
    Scaled(Box<NewExpression<F>>, F),
}

impl<F: PrimeField> NewExpression<F> {
    pub fn degree(
        &self,
        oracle_fn: &impl Fn(&OracleQuery) -> usize,
    ) -> usize {
        match self {
            NewExpression::Constant(_) => 0,
            NewExpression::Oracle(query) => oracle_fn(query),
            NewExpression::Negated(expr) => expr.degree(oracle_fn),
            NewExpression::Sum(lsh_expr, rhs_expr) => std::cmp::max(lsh_expr.degree(oracle_fn), rhs_expr.degree(oracle_fn)),
            NewExpression::Product(lsh_expr, rhs_expr) => lsh_expr.degree(oracle_fn) + rhs_expr.degree(oracle_fn),
            NewExpression::Scaled(expr, _) => expr.degree(oracle_fn),
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
            NewExpression::Constant(scalar) => constant_fn(*scalar),
            NewExpression::Oracle(query) => oracle_fn(query),
            NewExpression::Negated(a) => {
                let a = a.evaluate(constant_fn, oracle_fn, negated_fn, sum_fn, product_fn, scaled_fn);
                negated_fn(a)
            }
            NewExpression::Sum(a, b) => {
                let a = a.evaluate(constant_fn, oracle_fn, negated_fn, sum_fn, product_fn, scaled_fn);
                let b = b.evaluate(constant_fn, oracle_fn, negated_fn, sum_fn, product_fn, scaled_fn);
                sum_fn(a, b)
            }
            NewExpression::Product(a, b) => {
                let a = a.evaluate(constant_fn, oracle_fn, negated_fn, sum_fn, product_fn, scaled_fn);
                let b = b.evaluate(constant_fn, oracle_fn, negated_fn, sum_fn, product_fn, scaled_fn);
                product_fn(a, b)
            }
            NewExpression::Scaled(a, f) => {
                let a = a.evaluate(constant_fn, oracle_fn, negated_fn, sum_fn, product_fn, scaled_fn);
                scaled_fn(a, *f)
            }
        }
    }
}


impl<F: PrimeField> Neg for NewExpression<F> {
    type Output = NewExpression<F>;
    fn neg(self) -> Self::Output {
        NewExpression::Negated(Box::new(self))
    }
}

impl<F: PrimeField> Add for NewExpression<F> {
    type Output = NewExpression<F>;
    fn add(self, rhs: NewExpression<F>) -> NewExpression<F> {
        NewExpression::Sum(Box::new(self), Box::new(rhs))
    }
}

impl<F: PrimeField> Sub for NewExpression<F> {
    type Output = NewExpression<F>;
    fn sub(self, rhs: NewExpression<F>) -> NewExpression<F> {
        NewExpression::Sum(Box::new(self), Box::new(-rhs))
    }
}

impl<F: PrimeField> Mul for NewExpression<F> {
    type Output = NewExpression<F>;
    fn mul(self, rhs: NewExpression<F>) -> NewExpression<F> {
        NewExpression::Product(Box::new(self), Box::new(rhs))
    }
}

impl<F: PrimeField> Mul<F> for NewExpression<F> {
    type Output = NewExpression<F>;
    fn mul(self, rhs: F) -> NewExpression<F> {
        NewExpression::Scaled(Box::new(self), rhs)
    }
}

impl<F: PrimeField> From<OracleQuery> for NewExpression<F> {
    fn from(query: OracleQuery) -> Self {
        Self::Oracle(query)
    }
}

#[cfg(test)] 
mod test {
    #[test]
    fn test_new_expression() {
        
    }
}
