use super::piop::PIOPError;

#[derive(Debug)]
pub enum Error<E> {
    /// There was an error in the underlying polynomial commitment.
    PolynomialCommitmentError(E),

    /// There was an error in piop
    PIOPError(PIOPError),

    /// Pairing was evaluated as false
    OpeningCheckFailed
}

impl<E> Error<E> {
    /// Convert an error in the underlying polynomial commitment scheme
    /// to a `Error`.
    pub fn from_pc_err(err: E) -> Self {
        Self::PolynomialCommitmentError(err)
    }

    pub fn from_piop_err(err: PIOPError) -> Self {
        Error::PIOPError(err)
    }
}
