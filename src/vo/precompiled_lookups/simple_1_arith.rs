use std::marker::PhantomData;

use ark_ff::PrimeField;

use crate::{
    oracles::{query::OracleType, rotation::Rotation},
    vo::{query::VirtualQuery, virtual_expression::VirtualExpression},
};

use super::PrecompiledLookupVO;

pub struct PrecompiledSimple1ArithLookup<F: PrimeField> {
    _f: PhantomData<F>,
}

impl<F: PrimeField> PrecompiledLookupVO<F>
    for PrecompiledSimple1ArithLookup<F>
{
    fn get_expressions_and_queries() -> (
        Vec<crate::vo::virtual_expression::VirtualExpression<F>>,
        Vec<crate::vo::query::VirtualQuery>,
        Vec<crate::vo::query::VirtualQuery>,
    ) {
        let q1 = VirtualQuery::new(0, Rotation::curr(), OracleType::Witness);

        let t_q1 = VirtualQuery::new(0, Rotation::curr(), OracleType::Fixed);

        let expr1: VirtualExpression<F> = q1.clone().into();

        let expressions = vec![expr1];
        let queries = vec![q1];
        let table_queries = vec![t_q1];

        (expressions, queries, table_queries)
    }
}
