use std::marker::PhantomData;

use ark_ff::PrimeField;

use crate::{commitment::HomomorphicCommitment, rng::FiatShamirRng};

pub mod piop;
pub mod poly;

pub mod error;

pub struct Proof<F: PrimeField, PC: HomomorphicCommitment<F>> {
    // pub oracle_evaluations: Vec<F>,
    pub q_evals: Vec<F>,
    pub f_poly_commits: Vec<PC::Commitment>,
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
