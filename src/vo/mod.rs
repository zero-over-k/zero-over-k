use self::error::Error as VOError;
use self::expression::Expression;
use crate::oracles::query::OracleQuery;
use ark_ff::PrimeField;

pub mod error;
pub mod expression;
pub mod generic_lookup_vo;
pub mod generic_vo;
pub mod precompiled;
pub mod precompiled_lookups;
pub mod query;
pub mod virtual_expression;

// Note: VirtualOracle trait is very lightweight such that different use-cases
// can be built on top of this prover

/// Trait for specifying Virtual Oracle that should be included in batched zero over K check
pub trait VirtualOracle<F: PrimeField> {
    /// Returns expression that combines concrete oracles
    fn get_expression(&self) -> Result<&Expression<F>, VOError>;
}

// Note: LookupVirtualOracle is very lightweight such that different use-cases
// can be built on top of this prover

/// Lookup virtual oracle is defined as array of tuples: (expression, table_query) For now "right"
/// side is querying just fixed oracle, for more information see:
/// https://github.com/zcash/halo2/issues/534
pub trait LookupVirtualOracle<F: PrimeField> {
    fn get_expressions(&self) -> Result<&[Expression<F>], VOError>;

    fn get_table_queries(&self) -> Result<&[OracleQuery], VOError>;
}
