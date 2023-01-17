use crate::piop::error::Error as PiopError;
use ark_poly_commit::Error as ArkError;

#[derive(Debug)]
pub enum Error {
    /// There was an error in PIOP.
    PIOPError(PiopError),
    /// Pairing check does not hold.
    OpeningCheckFailed,
    /// Ark-poly-commit lib error
    ArkError(ArkError),
}

impl From<PiopError> for Error {
    fn from(err: PiopError) -> Self {
        Error::PIOPError(err)
    }
}

impl From<ArkError> for Error {
    fn from(err: ArkError) -> Self {
        Error::ArkError(err)
    }
}
