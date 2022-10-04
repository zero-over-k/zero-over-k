use ark_ff::PrimeField;
use ark_poly_commit::QuerySet;
use query::{InstanceQuery, WitnessQuery};

use self::expression::Expression;
pub mod error;
pub mod expression;
pub mod linearisation;
pub mod precompiled;
pub mod precompiled_vos;
pub mod query;

// Return expression that will be used to construct query set
pub trait ExpressionProvider<F: PrimeField> {
    fn get_expression_for_query_set(&self) -> &Expression<F>;
}

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

impl<F: PrimeField> ExpressionProvider<F> for dyn VirtualOracle<F> {
    fn get_expression_for_query_set(&self) -> &Expression<F> {
        self.get_expression()
    }
}

pub trait TestQueryVO<F: PrimeField> {
    /// Returns witness queries given virtual queries and assignment
    fn get_wtns_queries(&self) -> &[WitnessQuery];

    /// Returns instance queries given virtual queries and assignment
    fn get_instance_queries(&self) -> &[InstanceQuery];

    /// Returns expression that combines concrete oracles
    fn get_expression(&self) -> &Expression<F>;

    // fn get_query_set(&self) -> QuerySet<F> {
    //     let
    // }
}

#[cfg(test)]
mod test {
    pub trait A {
        fn f(&self) -> usize;
    }

    pub trait B {
        fn g(&self) -> usize;
    }

    impl A for dyn B {
        fn f(&self) -> usize {
            self.g()
        }
    }

    pub struct S {}

    impl B for S {
        fn g(&self) -> usize {
            3
        }
    }

    fn try_it<T: A>(x: T) -> usize {
        x.f()
    }

    #[test]
    fn test_a_b() {
        let s = S {};

        // println!("{}", try_it(s))

        // let ss: Vec<Box<dyn B>> = vec![Box::new(s)];

        // println!("{}", ss[0].f());
    }
}
