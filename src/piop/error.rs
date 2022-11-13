#[derive(Debug, PartialEq)]
pub enum Error {
    /// Missing evaluation at concrete oracle
    MissingConcreteEval(String),
    MissingExtendedEvals,
    /// Missing witness oracle with givien label
    MissingWtnsOracle(String),
    /// Missing fixed oracle with givien label
    MissingFixedOracle(String),
    /// Missing instance oracle with givien label
    MissingInstanceOracle(String),
    /// Query index exceeds witness oracle size
    WtnsQueryIndexOutOfBounds(usize),
    /// Query index exceeds instance oracle size
    InstanceQueryIndexOutOfBounds(usize),
}
