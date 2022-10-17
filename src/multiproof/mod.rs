use std::marker::PhantomData;

use ark_ff::PrimeField;

use crate::{commitment::HomomorphicCommitment, rng::FiatShamirRng};
use ark_serialize::{CanonicalSerialize, CanonicalDeserialize, SerializationError};
use ark_std::{
    io::{Read, Write},
};


pub mod piop;
pub mod poly;

pub mod error;

#[derive(CanonicalSerialize, CanonicalDeserialize)]
pub struct Proof<F: PrimeField, PC: HomomorphicCommitment<F>> {
    // pub oracle_evaluations: Vec<F>,
    pub q_evals: Vec<F>,
    pub f_commit: PC::Commitment,
    pub opening_proof: PC::Proof,
}

pub struct Multiproof<
    F: PrimeField,
    PC: HomomorphicCommitment<F>,
    FS: FiatShamirRng,
> {
    _f: PhantomData<F>,
    _pc: PhantomData<PC>,
    _fs: PhantomData<FS>,
}
