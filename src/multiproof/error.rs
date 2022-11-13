use crate::piop::error::Error as PiopError;
#[derive(Debug)]
pub enum Error<E> {
    /// There was an error in the underlying polynomial commitment.
    PolynomialCommitmentError(E),

    /// There was an error in piop
    PIOPError(PiopError),

    /// Pairing was evaluated as false
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
