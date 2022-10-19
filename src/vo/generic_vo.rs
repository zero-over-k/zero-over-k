use std::marker::PhantomData;

use ark_ff::PrimeField;

use crate::{
    commitment::HomomorphicCommitment,
    oracles::{
        query::{OracleQuery, OracleType},
        rotation::Rotation,
        traits::{ConcreteOracle, FixedOracle, InstanceOracle, WitnessOracle},
    },
};

use super::{
    new_expression::NewExpression, query::VirtualQuery,
    virtual_expression::VirtualExpression, VirtualOracle,
};

#[derive(Clone)]
pub struct GenericVO<F: PrimeField, PC: HomomorphicCommitment<F>> {
    pub(crate) virtual_exp: VirtualExpression<F>,
    pub(crate) virtual_queries: Vec<VirtualQuery>,
    pub(crate) queries: Option<Vec<OracleQuery>>,
    pub(crate) expression: Option<NewExpression<F>>,
    _pc: PhantomData<PC>,
}

impl<F: PrimeField, PC: HomomorphicCommitment<F>> GenericVO<F, PC> {
    pub fn init(cfg: (VirtualExpression<F>, Vec<VirtualQuery>)) -> Self {
        Self {
            virtual_exp: cfg.0,
            virtual_queries: cfg.1,
            queries: None,
            expression: None,
            _pc: PhantomData,
        }
    }

    pub fn configure(
        &mut self,
        witness_oracles: &mut [impl WitnessOracle<F>],
        instance_oracles: &mut [impl InstanceOracle<F>],
        fixed_oracles: &mut [impl FixedOracle<F>],
    ) {
        let mut queries = Vec::with_capacity(self.virtual_queries.len());
        for query in &self.virtual_queries {
            let oracle_query = match query.oracle_type {
                crate::oracles::query::OracleType::Witness => {
                    witness_oracles[query.index]
                        .register_rotation(query.rotation);
                    OracleQuery {
                        label: witness_oracles[query.index].get_label(),
                        rotation: query.rotation,
                        oracle_type: OracleType::Witness,
                    }
                }
                crate::oracles::query::OracleType::Instance => {
                    instance_oracles[query.index]
                        .register_rotation(query.rotation);
                    OracleQuery {
                        label: instance_oracles[query.index].get_label(),
                        rotation: query.rotation,
                        oracle_type: OracleType::Instance,
                    }
                }
                crate::oracles::query::OracleType::Fixed => {
                    fixed_oracles[query.index]
                        .register_rotation(query.rotation);
                    OracleQuery {
                        label: fixed_oracles[query.index].get_label(),
                        rotation: query.rotation,
                        oracle_type: OracleType::Fixed,
                    }
                }
            };

            queries.push(oracle_query);
        }

        self.queries = Some(queries.clone());
        self.expression = Some(self.virtual_exp.to_expression(
            witness_oracles,
            instance_oracles,
            fixed_oracles,
        ));
    }
}

impl<F: PrimeField, PC: HomomorphicCommitment<F>> VirtualOracle<F>
    for GenericVO<F, PC>
{
    fn get_queries(&self) -> &[OracleQuery] {
        match &self.queries {
            Some(queries) => &queries,
            None => panic!("Queries are not initialized"),
        }
    }

    fn get_expression(&self) -> &NewExpression<F> {
        match &self.expression {
            Some(expr) => &expr,
            None => panic!("Expression are not initialized"),
        }
    }
}
