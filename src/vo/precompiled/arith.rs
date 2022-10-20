use ark_ff::PrimeField;

use crate::{
    concrete_oracle::OracleType,
    vo::{
        expression::Expression,
        query::{InstanceQuery, Query, Rotation, VirtualQuery, WitnessQuery},
        VirtualOracle,
    },
};

// NOTE: Fixed columns are modeled as witness at the moment
/// Virtual Oracle for the arithmetization proposed in the original Plonk paper:
///   q_M(X) * a(X) * b(X)
/// + q_L(X) * a(X)
/// + q_R(X) * b(X)
/// + q_o(X) * c(X)
/// + q_c(X)
///                       + PI (X)
pub struct ArithVO<F: PrimeField> {
    virtual_queries: [VirtualQuery; 9],
    witness_indices: Option<Vec<usize>>,
    instance_indices: Option<Vec<usize>>,
    wtns_queries: Vec<WitnessQuery>,
    instance_queries: Vec<InstanceQuery>,
    queries: Vec<Box<dyn Query>>,
    expression: Option<Expression<F>>,
}

impl<F: PrimeField> ArithVO<F> {
    pub fn new() -> Self {
        let qm = VirtualQuery {
            index: 0,
            rotation: Rotation::curr(),
            oracle_type: OracleType::Witness,
        };

        let ql = VirtualQuery {
            index: 1,
            rotation: Rotation::curr(),
            oracle_type: OracleType::Witness,
        };

        let qr = VirtualQuery {
            index: 2,
            rotation: Rotation::curr(),
            oracle_type: OracleType::Witness,
        };

        let qo = VirtualQuery {
            index: 3,
            rotation: Rotation::curr(),
            oracle_type: OracleType::Witness,
        };

        let qc = VirtualQuery {
            index: 4,
            rotation: Rotation::curr(),
            oracle_type: OracleType::Witness,
        };

        let a = VirtualQuery {
            index: 5,
            rotation: Rotation::curr(),
            oracle_type: OracleType::Witness,
        };

        let b = VirtualQuery {
            index: 6,
            rotation: Rotation::curr(),
            oracle_type: OracleType::Witness,
        };

        let c = VirtualQuery {
            index: 7,
            rotation: Rotation::curr(),
            oracle_type: OracleType::Witness,
        };

        let pi = VirtualQuery {
            index: 0,
            rotation: Rotation::curr(),
            oracle_type: OracleType::Instance,
        };
        let virtual_queries = [qm, ql, qr, qo, qc, a, b, c, pi];

        Self {
            virtual_queries,
            witness_indices: None,
            instance_indices: None,
            wtns_queries: vec![],
            instance_queries: vec![],
            queries: vec![],
            expression: None,
        }
    }

    // TODO: consider abstracting
    pub fn configure(
        &mut self,
        witness_indices: &[usize; 8],
        instance_indices: &[usize; 1],
    ) {
        self.witness_indices = Some(vec![]);
        self.instance_indices = Some(vec![]);
        for vq in &self.virtual_queries {
            match vq.oracle_type {
                OracleType::Witness => {
                    let query = WitnessQuery {
                        index: witness_indices[vq.index],
                        rotation: vq.rotation.clone(),
                    };

                    self.wtns_queries.push(query);
                    self.queries.push(Box::new(query.clone()))
                }
                OracleType::Instance => {
                    let query = InstanceQuery {
                        index: instance_indices[vq.index],
                        rotation: vq.rotation.clone(),
                    };

                    self.instance_queries.push(query);
                    self.queries.push(Box::new(query.clone()))
                }
            }
        }

        let arith_expression = || {
            let qm: Expression<F> = self.wtns_queries[0].into();
            let ql: Expression<F> = self.wtns_queries[1].into();
            let qr: Expression<F> = self.wtns_queries[2].into();
            let qo: Expression<F> = self.wtns_queries[3].into();
            let qc: Expression<F> = self.wtns_queries[4].into();

            let a: Expression<F> = self.wtns_queries[5].into();
            let b: Expression<F> = self.wtns_queries[6].into();
            let c: Expression<F> = self.wtns_queries[7].into();

            let pi: Expression<F> = self.instance_queries[0].into();

            qm * a.clone() * b.clone() + ql * a + qr * b + qo * c + qc + pi
        };

        self.expression = Some(arith_expression());
    }
}

impl<F: PrimeField> VirtualOracle<F> for ArithVO<F> {
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

    fn get_queries(&self) -> &[Box<dyn Query>] {
        &self.queries
    }
}
