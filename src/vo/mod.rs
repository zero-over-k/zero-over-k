use ark_ff::PrimeField;
use query::{InstanceQuery, WitnessQuery};

use self::{expression::Expression};
pub mod expression;
pub mod precompiled;
pub mod precompiled_vos;
pub mod query;
pub mod error;

// Note: VirtualOracle trait is very lightweight such that different use-cases
// can be built on top of this prover

/// Trait for specifying Virtual Oracle that should be included in batched zero over K check
pub trait VirtualOracle<F: PrimeField> {
    /// Returns witness queries given virtual queries and assignment
    fn get_wtns_queries(&self) -> &[WitnessQuery];

    /// Returns instance queries given virtual queries and assignment
    fn get_instance_queries(&self) -> &[InstanceQuery];

    /// Returns expression that combines concrete oracles
    fn get_expression(&self) -> &Expression<F>;
}