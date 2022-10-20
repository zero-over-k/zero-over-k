use ark_ff::PrimeField;

use crate::oracles::query::OracleQuery;

use self::new_expression::NewExpression;

// use self::expression::Expression;
pub mod error;
// pub mod expression;
pub mod generic_vo;
pub mod new_expression;
pub mod precompiled;
pub mod query;
pub mod virtual_expression;

// Note: VirtualOracle trait is very lightweight such that different use-cases
// can be built on top of this prover

/// Trait for specifying Virtual Oracle that should be included in batched zero over K check
pub trait VirtualOracle<F: PrimeField> {
    fn get_queries(&self) -> &[OracleQuery];

    /// Returns expression that combines concrete oracles
    fn get_expression(&self) -> &NewExpression<F>;
}
