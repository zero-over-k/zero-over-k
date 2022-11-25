use super::rotation::Rotation;
use core::fmt;

#[derive(Clone)]
pub enum OracleType {
    Witness,
    Instance,
    Fixed,
    // TODO: add Selector
}

impl fmt::Display for OracleType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            OracleType::Witness => write!(f, "Witness oracle"),
            OracleType::Instance => write!(f, "Instance oracle"),
            OracleType::Fixed => write!(f, "Fixed oracle"),
        }
    }
}

#[derive(Clone)]
pub struct OracleQuery {
    pub label: String, //TODO: maybe consider: pub oracle: Box<&'a dyn ConcreteOracle<F>>,
    pub rotation: Rotation,
    pub oracle_type: OracleType,
}
