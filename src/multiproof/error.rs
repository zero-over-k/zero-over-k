use crate::piop::error::Error as PiopError;
#[derive(Debug)]
pub enum Error<E> {
    /// There was an error in the underlying polynomial commitment.
    PolynomialCommitmentError(E),

    /// There was an error in PIOP.
    PIOPError(PiopError),

    /// Pairing check does not hold.
    OpeningCheckFailed,
}

impl<E> From<PiopError> for Error<E> {
    fn from(err: PiopError) -> Self {
        Error::PIOPError(err)
    }
}
