use ark_ff::PrimeField;

use crate::oracles::{rotation::Rotation, query::OracleType};

use super::virtual_expression::VirtualExpression;

/// Virtual query is defined over relative oracle index that is being resolved
/// for concrete assignment
#[derive(Clone)]
pub struct VirtualQuery {
    pub(crate) index: usize,
    pub(crate) rotation: Rotation,
    pub(crate) oracle_type: OracleType,
}

impl VirtualQuery {
    pub fn new(
        index: usize,
        rotation: Rotation,
        oracle_type: OracleType,
    ) -> Self {
        Self {
            index,
            rotation,
            oracle_type,
        }
    }
}

impl<F: PrimeField> Into<VirtualExpression<F>> for VirtualQuery {
    fn into(self) -> VirtualExpression<F> {
        VirtualExpression::Oracle(self)
    }
}