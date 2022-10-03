use crate::iop::error::Error as IOPError;

/// A `enum` specifying the possible failure modes of the `SNARK`.
#[derive(Debug)]
pub enum Error<E> {
    /// The index is too large for the universal public parameters.
    IndexTooLarge,
    /// There was an error in the underlying holographic IOP.
    IOPError(IOPError),
    /// There was an error in the underlying polynomial commitment.
    PolynomialCommitmentError(E),
    /// Prover sent commitments to more chunks of quotient than needed
    TooManyChunks,
    /// Non zero over K indentity does not hold
    QuotientNotZero
}

impl<E> From<IOPError> for Error<E> {
    fn from(err: IOPError) -> Self {
        Error::IOPError(err)
    }
}

impl<E> Error<E> {
    /// Convert an error in the underlying polynomial commitment scheme
    /// to a `Error`.
    pub fn from_pc_err(err: E) -> Self {
        Error::PolynomialCommitmentError(err)
    }
}
