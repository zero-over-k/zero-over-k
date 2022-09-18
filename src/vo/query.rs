use crate::concrete_oracle::OracleType;

#[derive(PartialEq, PartialOrd, Eq, Ord, Clone)]
pub enum Sign {
    Plus,
    Minus,
}
/// Rotation can be positive or negative for an arbitrary degree
#[derive(PartialEq, PartialOrd, Eq, Ord, Clone)]
pub struct Rotation {
    pub(crate) degree: usize,
    pub(crate) sign: Sign,
}

impl Rotation {
    pub fn new(degree: usize, sign: Sign) -> Self {
        Self {
            degree,
            sign,
        }
    }

    // most common case is to use just curr, next and prev rotations
    pub fn curr() -> Self {
        Self {
            degree: 0,
            sign: Sign::Plus,
        }
    }

    pub fn next() -> Self {
        Self {
            degree: 1,
            sign: Sign::Plus,
        }
    }

    pub fn prev() -> Self {
        Self {
            degree: 1,
            sign: Sign::Minus,
        }
    }
}

/// Virtual query is defined over relative oracle index that is being resolved
/// for concrete assignment
#[derive(Clone)]
pub struct VirtualQuery {
    pub(crate) index: usize,
    pub(crate) rotation: Rotation,
    pub(crate) oracle_type: OracleType,
}

impl VirtualQuery {
    pub fn new(index: usize, rotation: Rotation, oracle_type: OracleType) -> Self {
        Self {
            index,
            rotation,
            oracle_type,
        }
    }
}

pub trait Query {
    fn get_type(&self) -> OracleType;
    fn get_index(&self) -> usize;
    fn get_rotation(&self) -> Rotation;
}

/// Witness query is concrete query of an witness oracle given the assignment
#[derive(PartialEq, PartialOrd, Eq, Ord, Clone)]
pub struct WitnessQuery {
    pub(crate) index: usize,
    pub(crate) rotation: Rotation,
}

impl WitnessQuery {
    pub fn new(index: usize, rotation: Rotation) -> Self {
        Self { index, rotation }
    }
}

impl Query for WitnessQuery {
    fn get_type(&self) -> OracleType {
        OracleType::Witness
    }

    fn get_index(&self) -> usize {
        self.index
    }

    fn get_rotation(&self) -> Rotation {
        self.rotation.clone()
    }
}

/// Instance query is concrete query of an instance oracle given the assignment
#[derive(PartialEq, PartialOrd, Eq, Ord, Clone)]
pub struct InstanceQuery {
    pub(crate) index: usize,
    pub(crate) rotation: Rotation,
}

impl InstanceQuery {
    pub fn new(index: usize, rotation: Rotation) -> Self {
        Self { index, rotation }
    }
}

impl Query for InstanceQuery {
    fn get_type(&self) -> OracleType {
        OracleType::Instance
    }

    fn get_index(&self) -> usize {
        self.index
    }

    fn get_rotation(&self) -> Rotation {
        self.rotation.clone()
    }
}
