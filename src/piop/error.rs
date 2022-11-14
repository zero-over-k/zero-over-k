#[derive(Debug, PartialEq)]
pub enum Error {
    /// Missing commiment.
    MissingWtnsCommitment(String),
    /// Missing fixed commiment.
    MissingFixedCommitment(String),
    /// Missing instance commiment.
    MissingInstanceCommitment(String),
    /// Missing evaluation at concrete oracle.
    MissingConcreteEval(String),
    /// Missing extended coset evaluations for witness oracle.
    MissingCosetWtnsEval(String),
    /// Missing extended coset evaluations for fixed oracle.
    MissingCosetFixedEval(String),
    /// Missing extended coset evaluations for instance oracle.
    MissingCosetInstanceEval(String),
    MissingExtendedEvals,
    /// Missing witness oracle with givien label.
    MissingWtnsOracle(String),
    /// Missing fixed oracle with givien label.
    MissingFixedOracle(String),
    /// Missing instance oracle with givien label.
    MissingInstanceOracle(String),
    /// Missing permutation argument oracle.
    MissingPermutationOracle(String),
    /// Missing LookUp table oracle.
    MissingLUTableOracle(String),
    /// Query index exceeds witness oracle size.
    WtnsQueryIndexOutOfBounds(usize),
    /// Query index exceeds instance oracle size.
    InstanceQueryIndexOutOfBounds(usize),
    //see: https:github.com/zcash/halo2/issues/534
    WtnsTableNotAllowed(String),
    //see: https:github.com/zcash/halo2/issues/534
    InstanceTableNotAllowed(String),
}
