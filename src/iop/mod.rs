pub mod error;
pub mod prover;
pub mod verifier;

use ark_ff::PrimeField;
use std::marker::PhantomData;

use crate::commitment::HomomorphicCommitment;

pub struct PIOPforPolyIdentity<F: PrimeField, PC: HomomorphicCommitment<F>> {
    _field: PhantomData<F>,
    _pc: PhantomData<PC>,
}
