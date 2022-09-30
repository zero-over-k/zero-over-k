use ark_ff::PrimeField;
use query::{InstanceQuery, WitnessQuery};

use crate::concrete_oracle::OracleType;

use self::query::VirtualQuery;
pub mod query;
pub mod expression;

// Note: VirtualOracle trait is very undeterministic and lightweight such that different usecases
// can be built on top of this prover

/// Trait for specifying Virtual Oracle that should be included in batched zero over K check
pub trait VirtualOracle<F: PrimeField> {
    /// Returns witness queries given virtual queries and assignment
    fn get_wtns_queries(&self) -> &[WitnessQuery];

    /// Returns instance queries given virtual queries and assignment
    fn get_instance_queries(&self) -> &[InstanceQuery];

    /// TODO: this we want to automate with Abstract Syntax tree
    /// Hardcoded implementation for degree calculation
    fn compute_degree(&self, wtns_degrees: &Vec<usize>, instance_degrees: &Vec<usize>) -> usize;

    /// VO encodes constraint that must go to zero
    fn constraint_function(&self, x: F, wtns_evals: &Vec<F>, instance_evals: &Vec<F>) -> F;
}

pub struct GenericVO<F: PrimeField> {
    virtual_queries: Vec<VirtualQuery>,
    witness_indices: Option<Vec<usize>>, 
    instance_indices: Option<Vec<usize>>, 
    wtns_queries: Vec<WitnessQuery>, 
    instance_queries: Vec<InstanceQuery>, 
    degree_func: fn (wtns_degrees: &Vec<usize>, instance_degrees: &Vec<usize>) -> usize,
    constraint_function: fn (x: F, wtns_evals: &Vec<F>, instance_evals: &Vec<F>) -> F
}

impl<F: PrimeField> GenericVO<F> {
    pub fn new(
        virtual_queries: &Vec<VirtualQuery>, 
        degree_func: fn (wtns_degrees: &Vec<usize>, instance_degrees: &Vec<usize>) -> usize,
        constraint_function: fn (x: F, wtns_evals: &Vec<F>, instance_evals: &Vec<F>) -> F
    ) -> Self {
        Self {
            virtual_queries: virtual_queries.clone(), 
            witness_indices: None, 
            instance_indices: None, 
            wtns_queries: vec![], 
            instance_queries: vec![], 
            degree_func,
            constraint_function
        }
    }

    pub fn assign_concrete_oracles(&mut self, witness_indices: Vec<usize>, instance_indices: Vec<usize>) {
        for vq in &self.virtual_queries {
            match vq.oracle_type {
                OracleType::Witness => self.wtns_queries.push(WitnessQuery { index: witness_indices[vq.index], rotation: vq.rotation.clone() }), 
                OracleType::Instance => self.instance_queries.push(InstanceQuery { index: instance_indices[vq.index], rotation: vq.rotation.clone() })
            }
        }

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

    fn compute_degree(&self, wtns_degrees: &Vec<usize>, instance_degrees: &Vec<usize>) -> usize {
        (self.degree_func)(wtns_degrees, instance_degrees)
    }

    fn constraint_function(&self, x: F, wtns_evals: &Vec<F>, instance_evals: &Vec<F>) -> F {
        (self.constraint_function)(x, wtns_evals, instance_evals)
    }
}

#[cfg(test)]
mod test {
    use crate::concrete_oracle::OracleType;

    use super::{VirtualOracle, query::{VirtualQuery, WitnessQuery, InstanceQuery}};
    use ark_bls12_381::Fr;
    use ark_ff::PrimeField;
}
