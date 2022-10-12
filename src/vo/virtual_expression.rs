use std::ops::{Add, Mul, Neg, Sub};

use ark_ff::PrimeField;

use crate::oracles::{
    query::{OracleQuery, OracleType},
    traits::ConcreteOracle,
    witness,
};

use super::{new_expression::NewExpression, query::VirtualQuery};

#[derive(Clone)]
pub enum VirtualExpression<F> {
    Constant(F),
    Oracle(VirtualQuery),
    Negated(Box<VirtualExpression<F>>),
    Sum(Box<VirtualExpression<F>>, Box<VirtualExpression<F>>),
    Product(Box<VirtualExpression<F>>, Box<VirtualExpression<F>>),
    Scaled(Box<VirtualExpression<F>>, F),
}

impl<F: PrimeField> VirtualExpression<F> {
    pub fn to_expression(
        &self,
        witness_oracles: &[impl ConcreteOracle<F>],
        instance_oracles: &[impl ConcreteOracle<F>],
        fixed_oracles: &[impl ConcreteOracle<F>],
    ) -> NewExpression<F> {
        match self {
            VirtualExpression::Constant(f) => NewExpression::Constant(*f),
            VirtualExpression::Oracle(query) => {
                let oracle_query = match query.oracle_type {
                    crate::oracles::query::OracleType::Witness => OracleQuery {
                        label: witness_oracles[query.index].get_label(),
                        rotation: query.rotation,
                        oracle_type: OracleType::Witness,
                    },
                    crate::oracles::query::OracleType::Instance => {
                        OracleQuery {
                            label: instance_oracles[query.index].get_label(),
                            rotation: query.rotation,
                            oracle_type: OracleType::Instance,
                        }
                    }
                    crate::oracles::query::OracleType::Fixed => OracleQuery {
                        label: fixed_oracles[query.index].get_label(),
                        rotation: query.rotation,
                        oracle_type: OracleType::Fixed,
                    },
                };

                NewExpression::Oracle(oracle_query)
            }
            VirtualExpression::Negated(expr) => {
                let expr = expr.to_expression(
                    witness_oracles,
                    instance_oracles,
                    fixed_oracles,
                );
                NewExpression::Negated(Box::new(expr))
            }
            VirtualExpression::Sum(lhs_expr, rhs_expr) => {
                let lhs_expr = lhs_expr.to_expression(
                    witness_oracles,
                    instance_oracles,
                    fixed_oracles,
                );
                let rhs_expr = rhs_expr.to_expression(
                    witness_oracles,
                    instance_oracles,
                    fixed_oracles,
                );
                NewExpression::Sum(Box::new(lhs_expr), Box::new(rhs_expr))
            }
            VirtualExpression::Product(lhs_expr, rhs_expr) => {
                let lhs_expr = lhs_expr.to_expression(
                    witness_oracles,
                    instance_oracles,
                    fixed_oracles,
                );
                let rhs_expr = rhs_expr.to_expression(
                    witness_oracles,
                    instance_oracles,
                    fixed_oracles,
                );
                NewExpression::Product(Box::new(lhs_expr), Box::new(rhs_expr))
            }
            VirtualExpression::Scaled(expr, f) => {
                let expr = expr.to_expression(
                    witness_oracles,
                    instance_oracles,
                    fixed_oracles,
                );
                NewExpression::Scaled(Box::new(expr), *f)
            }
        }
    }
}

impl<F: PrimeField> Neg for VirtualExpression<F> {
    type Output = VirtualExpression<F>;
    fn neg(self) -> Self::Output {
        VirtualExpression::Negated(Box::new(self))
    }
}

impl<F: PrimeField> Add for VirtualExpression<F> {
    type Output = VirtualExpression<F>;
    fn add(self, rhs: VirtualExpression<F>) -> VirtualExpression<F> {
        VirtualExpression::Sum(Box::new(self), Box::new(rhs))
    }
}

impl<F: PrimeField> Sub for VirtualExpression<F> {
    type Output = VirtualExpression<F>;
    fn sub(self, rhs: VirtualExpression<F>) -> VirtualExpression<F> {
        VirtualExpression::Sum(Box::new(self), Box::new(-rhs))
    }
}

impl<F: PrimeField> Mul for VirtualExpression<F> {
    type Output = VirtualExpression<F>;
    fn mul(self, rhs: VirtualExpression<F>) -> VirtualExpression<F> {
        VirtualExpression::Product(Box::new(self), Box::new(rhs))
    }
}

impl<F: PrimeField> Mul<F> for VirtualExpression<F> {
    type Output = VirtualExpression<F>;
    fn mul(self, rhs: F) -> VirtualExpression<F> {
        VirtualExpression::Scaled(Box::new(self), rhs)
    }
}

#[cfg(test)]
mod test {
    #[test]
    fn test_new_expression() {}
}
