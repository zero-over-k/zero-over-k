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

impl<E> Error<E> {
    /// Convert an error in the underlying polynomial commitment scheme
    /// to a `Error`.
    pub fn from_pc_err(err: E) -> Self {
        Self::PolynomialCommitmentError(err)
    }
}

impl<E> From<PiopError> for Error<E> {
    fn from(err: PiopError) -> Self {
        Error::PIOPError(err)
    }
}
