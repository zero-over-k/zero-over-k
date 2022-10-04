pub mod error;
pub mod prover;
pub mod verifier;

use std::marker::PhantomData;
use ark_ff::PrimeField;

pub struct IOPforPolyIdentity<F: PrimeField> {
    _field: PhantomData<F>,
}