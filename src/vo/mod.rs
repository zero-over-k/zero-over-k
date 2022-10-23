use ark_ff::PrimeField;

use crate::oracles::query::OracleQuery;

use self::new_expression::NewExpression;

// use self::expression::Expression;
pub mod error;
// pub mod expression;
pub mod generic_vo;
pub mod new_expression;
pub mod precompiled;
pub mod precompiled_lookups;
pub mod query;
pub mod virtual_expression;
pub mod generic_lookup_vo;

// Note: VirtualOracle trait is very lightweight such that different use-cases
// can be built on top of this prover

/// Trait for specifying Virtual Oracle that should be included in batched zero over K check
pub trait VirtualOracle<F: PrimeField> {
    /// after introducing query mapping in configure we don't need queries anymore
    // fn get_queries(&self) -> &[OracleQuery];

    /// Returns expression that combines concrete oracles
    fn get_expression(&self) -> &NewExpression<F>;
}

// Note: LookupVirtualOracle is very lightweight such that different use-cases
// can be built on top of this prover

/// Lookup virtual oracle is defined as array of tuples: (expression, table_query)
/// For now "right" side is querying just fixed oracle, for more information see: https://github.com/zcash/halo2/issues/534
pub trait LookupVirtualOracle<F: PrimeField> {
    fn get_expressions(&self) -> &[NewExpression<F>];

    fn get_table_queries(&self) -> &[OracleQuery];
}
