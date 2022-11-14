use super::{query::VirtualQuery, virtual_expression::VirtualExpression};
use ark_ff::PrimeField;

pub trait PrecompiledVO<F: PrimeField> {
    fn get_expr_and_queries() -> (VirtualExpression<F>, Vec<VirtualQuery>);
}

pub mod logic;
pub mod mul;
pub mod plonk_arith;
pub mod rescue;

#[cfg(test)]
pub(crate) mod tests;
