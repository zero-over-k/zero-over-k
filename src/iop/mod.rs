pub mod error;
pub mod prover;
pub mod verifier;

use ark_ff::PrimeField;
use std::marker::PhantomData;

pub struct IOPforPolyIdentity<F: PrimeField> {
    _field: PhantomData<F>,
}
