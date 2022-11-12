use super::{
    expression::Expression, query::VirtualQuery,
    virtual_expression::VirtualExpression, LookupVirtualOracle,
};
use crate::oracles::{
    query::{OracleQuery, OracleType},
    traits::{FixedOracle, InstanceOracle, WitnessOracle},
};
use ark_ff::PrimeField;

#[derive(Clone)]
pub struct GenericLookupVO<F: PrimeField> {
    pub(crate) virtual_expressions: Vec<VirtualExpression<F>>,
    pub(crate) virtual_queries: Vec<VirtualQuery>,
    pub(crate) virtual_table_queries: Vec<VirtualQuery>, // for now table query is just querying of fixed oracle, later we can introduce TableOracle, TableQuery, etc...
    pub(crate) table_queries: Option<Vec<OracleQuery>>,
    pub(crate) expressions: Option<Vec<Expression<F>>>,
}

impl<F: PrimeField> GenericLookupVO<F> {
    pub fn init(
        cfg: (
            Vec<VirtualExpression<F>>,
            Vec<VirtualQuery>,
            Vec<VirtualQuery>,
        ),
    ) -> Self {
        Self {
            virtual_expressions: cfg.0,
            virtual_queries: cfg.1,
            virtual_table_queries: cfg.2,
            table_queries: None,
            expressions: None,
        }
    }

    pub fn configure(
        &mut self,
        witness_oracles: &mut [impl WitnessOracle<F>],
        instance_oracles: &mut [impl InstanceOracle<F>],
        fixed_oracles: &mut [impl FixedOracle<F>],
        table_oracles: &mut [impl FixedOracle<F>],
    ) {
        for query in &self.virtual_queries {
            match query.oracle_type {
                crate::oracles::query::OracleType::Witness => {
                    witness_oracles[query.index]
                        .register_rotation(query.rotation);
                }
                crate::oracles::query::OracleType::Instance => {
                    instance_oracles[query.index]
                        .register_rotation(query.rotation);
                }
                crate::oracles::query::OracleType::Fixed => {
                    fixed_oracles[query.index]
                        .register_rotation(query.rotation);
                }
            };
        }

        let mut table_queries =
            Vec::<OracleQuery>::with_capacity(self.virtual_table_queries.len());
        for query in &self.virtual_table_queries {
            match query.oracle_type {
                OracleType::Witness => panic!(
                    "Witness query is not allowed to serve as table query"
                ), //see: https:github.com/zcash/halo2/issues/534
                OracleType::Instance => panic!(
                    "Instance query is not allowed to serve as table query"
                ), //see: https:github.com/zcash/halo2/issues/534
                OracleType::Fixed => {
                    table_oracles[query.index]
                        .register_rotation(query.rotation);
                    table_queries.push(OracleQuery {
                        label: table_oracles[query.index].get_label().clone(),
                        rotation: query.rotation,
                        oracle_type: OracleType::Fixed,
                    })
                }
            }
        }

        let expressions: Vec<Expression<F>> = self
            .virtual_expressions
            .iter()
            .map(|v_exp| {
                v_exp.to_expression(
                    witness_oracles,
                    instance_oracles,
                    fixed_oracles,
                )
            })
            .collect();

        self.expressions = Some(expressions);
        self.table_queries = Some(table_queries);
    }
}

impl<F: PrimeField> LookupVirtualOracle<F> for GenericLookupVO<F> {
    fn get_expressions(&self) -> &[Expression<F>] {
        match &self.expressions {
            Some(expressions) => &expressions,
            None => panic!("table queries are not defined"),
        }
    }

    fn get_table_queries(&self) -> &[OracleQuery] {
        match &self.table_queries {
            Some(queries) => &queries,
            None => panic!("table queries are not defined"),
        }
    }
}
