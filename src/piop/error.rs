use crate::oracles::rotation::Rotation;
use crate::vo::error::Error as VOError;

#[derive(Debug, PartialEq, Eq)]
pub enum Error {
    /// Missing commiment.
    MissingWitnessCommitment(String),
    /// Missing fixed commiment.
    MissingFixedCommitment(String),
    /// Missing instance commiment.
    MissingInstanceCommitment(String),
    /// Missing evaluation at concrete oracle.
    MissingConcreteEval(String),
    /// Missing extended coset evaluations for witness oracle.
    MissingCosetWitnessEval(String),
    /// Missing extended coset evaluations for fixed oracle.
    MissingCosetFixedEval(String),
    /// Missing extended coset evaluations for instance oracle.
    MissingCosetInstanceEval(String),
    MissingExtendedEvals,
    /// Missing witness oracle with givien label.
    MissingWitnessOracle(String),
    /// Missing fixed oracle with givien label.
    MissingFixedOracle(String),
    /// Missing instance oracle with givien label.
    MissingInstanceOracle(String),
    /// Missing permutation argument oracle.
    MissingPermutationOracle(String),
    /// Missing LookUp table oracle.
    MissingLookupTableOracle(String),
    /// Query index exceeds witness oracle size.
    WitnessQueryIndexOutOfBounds(usize),
    /// Query index exceeds instance oracle size.
    InstanceQueryIndexOutOfBounds(usize),
    /// Non-constant tables not supported.
    //This feaure may get introduced in the future
    //see: https:github.com/zcash/halo2/issues/534
    WitnessTableNotAllowed(String),
    /// Non-constant tables not supported.
    //This feaure may get introduced in the future
    //see: https:github.com/zcash/halo2/issues/534
    InstanceTableNotAllowed(String),
    /// Rotations of challenge result in the same point.
    RepeatedRotation(Rotation),
    /// Virtual Oracle error
    VOError(VOError),
}

impl From<VOError> for Error {
    fn from(err: VOError) -> Self {
        Error::VOError(err)
    }
}
