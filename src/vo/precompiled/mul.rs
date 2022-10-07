use ark_ff::PrimeField;

use crate::{
    concrete_oracle::OracleType,
    vo::{
        expression::Expression,
        query::{InstanceQuery, Rotation, VirtualQuery, WitnessQuery},
        VirtualOracle,
    },
};

pub struct MulVO<F: PrimeField> {
    virtual_queries: [VirtualQuery; 3],
    witness_indices: Option<Vec<usize>>,
    instance_indices: Option<Vec<usize>>,
    wtns_queries: Vec<WitnessQuery>,
    instance_queries: Vec<InstanceQuery>,
    expression: Option<Expression<F>>,
}

impl<F: PrimeField> MulVO<F> {
    pub fn new() -> Self {
        let q1 = VirtualQuery {
            index: 0,
            rotation: Rotation::curr(),
            oracle_type: OracleType::Witness,
        };

        let q2 = VirtualQuery {
            index: 1,
            rotation: Rotation::curr(),
            oracle_type: OracleType::Witness,
        };

        let q3 = VirtualQuery {
            index: 0,
            rotation: Rotation::curr(),
            oracle_type: OracleType::Instance,
        };
        let virtual_queries = [q1, q2, q3];

        Self {
            virtual_queries,
            witness_indices: None,
            instance_indices: None,
            wtns_queries: vec![],
            instance_queries: vec![],
            expression: None,
        }
    }

    // TODO: consider abstracting
    pub fn configure(
        &mut self,
        witness_indices: &[usize; 2],
        instance_indices: &[usize; 1],
    ) {
        self.witness_indices = Some(vec![]);
        self.instance_indices = Some(vec![]);
        for vq in &self.virtual_queries {
            match vq.oracle_type {
                OracleType::Witness => self.wtns_queries.push(WitnessQuery {
                    index: witness_indices[vq.index],
                    rotation: vq.rotation.clone(),
                }),
                OracleType::Instance => {
                    self.instance_queries.push(InstanceQuery {
                        index: instance_indices[vq.index],
                        rotation: vq.rotation.clone(),
                    })
                }
            }
        }

        let mul_expression = || {
            let a: Expression<F> = self.wtns_queries[0].into();
            let b: Expression<F> = self.wtns_queries[1].into();
            let c: Expression<F> = self.instance_queries[0].into();

            a * b - c
        };

        self.expression = Some(mul_expression());
    }
}

impl<F: PrimeField> VirtualOracle<F> for MulVO<F> {
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