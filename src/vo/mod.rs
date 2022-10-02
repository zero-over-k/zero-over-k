use ark_ff::PrimeField;
use query::{InstanceQuery, WitnessQuery};

use crate::concrete_oracle::OracleType;

use self::{expression::Expression, query::VirtualQuery};
pub mod expression;
pub mod query;

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

pub struct GenericVO<F: PrimeField> {
    virtual_queries: Vec<VirtualQuery>,
    witness_indices: Option<Vec<usize>>,
    instance_indices: Option<Vec<usize>>,
    wtns_queries: Vec<WitnessQuery>,
    instance_queries: Vec<InstanceQuery>,
    expression: Option<Expression<F>>,
    expression_func:
        fn(wnts_queries: &[Expression<F>], instance_queries: &[Expression<F>]) -> Expression<F>,
}

impl<F: PrimeField> GenericVO<F> {
    pub fn new(
        virtual_queries: &Vec<VirtualQuery>,
        degree_func: fn(wtns_degrees: &Vec<usize>, instance_degrees: &Vec<usize>) -> usize,
        constraint_function: fn(x: F, wtns_evals: &Vec<F>, instance_evals: &Vec<F>) -> F,
        expression_func: fn(
            wnts_queries: &[Expression<F>],
            instance_queries: &[Expression<F>],
        ) -> Expression<F>,
    ) -> Self {
        Self {
            virtual_queries: virtual_queries.clone(),
            witness_indices: None,
            instance_indices: None,
            wtns_queries: vec![],
            instance_queries: vec![],
            expression: None,
            expression_func,
        }
    }

    pub fn assign_concrete_oracles(
        &mut self,
        witness_indices: Vec<usize>,
        instance_indices: Vec<usize>,
    ) {
        for vq in &self.virtual_queries {
            match vq.oracle_type {
                OracleType::Witness => self.wtns_queries.push(WitnessQuery {
                    index: witness_indices[vq.index],
                    rotation: vq.rotation.clone(),
                }),
                OracleType::Instance => self.instance_queries.push(InstanceQuery {
                    index: instance_indices[vq.index],
                    rotation: vq.rotation.clone(),
                }),
            }
        }

        let wtns_expressions: Vec<Expression<F>> = self
            .wtns_queries
            .iter()
            .map(|query| Expression::<F>::Witness(query.clone()))
            .collect();
        let instance_expressions: Vec<Expression<F>> = self
            .instance_queries
            .iter()
            .map(|query| Expression::<F>::Instance(query.clone()))
            .collect();

        self.expression = Some((self.expression_func)(
            &wtns_expressions,
            &instance_expressions,
        ));

        self.witness_indices = Some(witness_indices);
        self.instance_indices = Some(instance_indices);
    }
}

impl<F: PrimeField> VirtualOracle<F> for GenericVO<F> {
    fn get_wtns_queries(&self) -> &[WitnessQuery] {
        &self.wtns_queries
    }

    fn get_instance_queries(&self) -> &[InstanceQuery] {
        &self.instance_queries
    }

    // panics if expression is not defined before proving started
    fn get_expression(&self) -> &Expression<F> {
        match self.expression.as_ref() {
            None => panic!("Expression is not defined"),
            Some(expression) => return expression,
        }
    }
}

#[cfg(test)]
mod test {
    use crate::concrete_oracle::OracleType;

    use super::{
        query::{InstanceQuery, VirtualQuery, WitnessQuery},
        VirtualOracle,
    };
    use ark_bls12_381::Fr;
    use ark_ff::PrimeField;
}
