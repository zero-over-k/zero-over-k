use std::marker::PhantomData;

use ark_ff::PrimeField;

use crate::{vo::{query::VirtualQuery, virtual_expression::VirtualExpression}, oracles::{rotation::Rotation, query::OracleType}};

use super::PrecompiledLookupVO;

pub struct PrecompiledSimple3ArithLookup<F: PrimeField> {
    _f: PhantomData<F>
}

impl<F: PrimeField> PrecompiledLookupVO<F> for PrecompiledSimple3ArithLookup<F> {
    fn get_expressions_and_queries() -> (Vec<crate::vo::virtual_expression::VirtualExpression<F>>, Vec<crate::vo::query::VirtualQuery>, Vec<crate::vo::query::VirtualQuery>) {
        let q1 = VirtualQuery::new(0, Rotation::curr(), OracleType::Witness);
        let q2 = VirtualQuery::new(1, Rotation::curr(), OracleType::Witness);
        let q3 = VirtualQuery::new(2, Rotation::curr(), OracleType::Witness);

        let t_q1 = VirtualQuery::new(0, Rotation::curr(), OracleType::Fixed);
        let t_q2 = VirtualQuery::new(1, Rotation::curr(), OracleType::Fixed);
        let t_q3 = VirtualQuery::new(2, Rotation::curr(), OracleType::Fixed);

        let expr1: VirtualExpression<F> = q1.clone().into();
        let expr2: VirtualExpression<F> = q2.clone().into();
        let expr3: VirtualExpression<F> = q3.clone().into();

        let expressions = vec![expr1, expr2, expr3];
        let queries = vec![q1, q2, q3];
        let table_queries = vec![t_q1, t_q2, t_q3];

        (expressions, queries, table_queries)
    }
}