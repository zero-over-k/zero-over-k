use crate::oracles::{query::OracleType, rotation::Rotation};

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
