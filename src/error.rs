use crate::multiproof::error::Error as MultiproofError;
use crate::piop::error::Error as IOPError;
use crate::vo::error::Error as VOError;
use ark_poly_commit::Error as ArkPolyCommitError;

/// A `enum` specifying the possible failure modes of the `SNARK`.
#[derive(Debug)]
pub enum Error {
    /// The index is too large for the universal public parameters.
    IndexTooLarge,
    /// There was an error in the underlying holographic IOP.
    IOPError(IOPError),
    /// There was an error in an underlying Virtual Oracle.
    VOError(VOError),
    /// There was an error in the underlying polynomial commitment.
    ArkPolyCommitError(ArkPolyCommitError),
    /// Prover sent commitments to more or less chunks of quotient than needed
    WrongNumberOfChunks,
    /// Non zero over K indentity does not hold
    QuotientNotZero,
    MultiproofError(MultiproofError),

    QuotientTooSmall,
}

impl From<IOPError> for Error {
    fn from(err: IOPError) -> Self {
        Error::IOPError(err)
    }
}

impl From<VOError> for Error {
    fn from(err: VOError) -> Self {
        Error::VOError(err)
    }
}

impl From<ArkPolyCommitError> for Error {
    fn from(err: ArkPolyCommitError) -> Self {
        Error::ArkPolyCommitError(err)
    }
}

impl From<MultiproofError> for Error {
    fn from(err: MultiproofError) -> Self {
        Error::MultiproofError(err)
    }
}
