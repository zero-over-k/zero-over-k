use crate::oracles::{
    query::{OracleQuery, OracleType},
    traits::{FixedOracle, InstanceOracle, WitnessOracle},
};
use crate::vo::{
    error::Error as VOError, expression::Expression, query::VirtualQuery,
    virtual_expression::VirtualExpression, VirtualOracle,
};
use ark_ff::PrimeField;

#[derive(Clone)]
pub struct GenericVO<F: PrimeField> {
    pub(crate) virtual_exp: VirtualExpression<F>,
    pub(crate) virtual_queries: Vec<VirtualQuery>,
    pub(crate) queries: Option<Vec<OracleQuery>>,
    pub(crate) expression: Option<Expression<F>>,
}

impl<F: PrimeField> GenericVO<F> {
    pub fn init(cfg: (VirtualExpression<F>, Vec<VirtualQuery>)) -> Self {
        Self {
            virtual_exp: cfg.0,
            virtual_queries: cfg.1,
            queries: None,
            expression: None,
        }
    }

    pub fn configure(
        &mut self,
        witness_oracles: &mut [&mut impl WitnessOracle<F>],
        instance_oracles: &mut [&mut impl InstanceOracle<F>],
        fixed_oracles: &mut [&mut impl FixedOracle<F>],
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

impl<F: PrimeField> VirtualOracle<F> for GenericVO<F> {
    fn get_expression(&self) -> Result<&Expression<F>, VOError> {
        match &self.expression {
            Some(expr) => Ok(&expr),
            None => Err(VOError::UninitializedExpr),
        }
    }
}
