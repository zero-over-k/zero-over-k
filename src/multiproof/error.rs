use crate::piop::error::Error as PiopError;

#[derive(Debug)]
pub enum Error {
    /// There was an error in the underlying polynomial commitment.
    PolynomialCommitmentError,

    /// There was an error in PIOP.
    PIOPError(PiopError),

    /// Pairing check does not hold.
    OpeningCheckFailed,
}

impl From<PiopError> for Error {
    fn from(err: PiopError) -> Self {
        Error::PIOPError(err)
    }
}
