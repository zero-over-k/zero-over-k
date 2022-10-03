use ark_ff::PrimeField;
use query::{InstanceQuery, WitnessQuery};

use crate::concrete_oracle::OracleType;

use self::{expression::Expression, query::VirtualQuery};
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

#[cfg(test)]
mod test {
    use crate::concrete_oracle::OracleType;

    use super::{
        expression::Expression,
        query::{InstanceQuery, Rotation, VirtualQuery, WitnessQuery},
        VirtualOracle,
    };
    use ark_bls12_381::Fr as F;
    use ark_ff::PrimeField;

    #[test]
    fn test_simple_oracle() {
        let q1 = VirtualQuery {
            index: 0,
            rotation: Rotation::curr(),
            oracle_type: OracleType::Witness,
        };

        let q2 = VirtualQuery {
            index: 1,
            rotation: Rotation::curr(),
            oracle_type: OracleType::Instance,
        };

        let q3 = VirtualQuery {
            index: 2,
            rotation: Rotation::curr(),
            oracle_type: OracleType::Instance,
        };

        // let mul_vo = MulVO::<F>::new([q1, q2, q3]);
    }
}
