#[derive(Debug, PartialEq)]
pub enum Error {
    /// Missing commiment
    MissingWtnsCommitment(String),
    /// Missing fixed commiment
    MissingFixedCommitment(String),
    /// Missing instance commiment
    MissingInstanceCommitment(String),
    /// Missing evaluation at concrete oracle
    MissingConcreteEval(String),
    MissingExtendedEvals,
    /// Missing witness oracle with givien label
    MissingWtnsOracle(String),
    /// Missing fixed oracle with givien label
    MissingFixedOracle(String),
    /// Missing instance oracle with givien label
    MissingInstanceOracle(String),
    /// Missing permutation argument oracle
    MissingPermutationOracle(String),
    /// Missing LookUp table oracle
    MissingLUTableOracle(String),
    /// Query index exceeds witness oracle size
    WtnsQueryIndexOutOfBounds(usize),
    /// Query index exceeds instance oracle size
    InstanceQueryIndexOutOfBounds(usize),

    // TODO doc
    WtnsTableNotAllowed(String),
    // TODO doc
    InstanceTableNotAllowed(String),
}
