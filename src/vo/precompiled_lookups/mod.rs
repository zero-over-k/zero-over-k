use ark_ff::PrimeField;

use super::{query::VirtualQuery, virtual_expression::VirtualExpression};

pub mod simple;

/// return expressions, queries and table queries
pub trait PrecompiledLookupVO<F: PrimeField> {
    fn get_expressions_and_queries() -> (
        Vec<VirtualExpression<F>>,
        Vec<VirtualQuery>,
        Vec<VirtualQuery>,
    );
}
