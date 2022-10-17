use ark_ff::PrimeField;
use ark_poly::{univariate::DensePolynomial, GeneralEvaluationDomain};
use ark_poly_commit::{PolynomialCommitment, PCRandomness};

use crate::{
    commitment::HomomorphicCommitment, multiproof::Proof as MultiOpenProof,
    oracles::fixed::FixedOracle,
};

pub type UniversalSRS<F, PC> =
    <PC as PolynomialCommitment<F, DensePolynomial<F>>>::UniversalParams;

#[derive(Clone)]
pub struct IndexInfo<F: PrimeField> {
    pub quotient_degree: usize,
    pub extended_coset_domain: GeneralEvaluationDomain<F>,
}

pub struct VerifierKey<F: PrimeField, PC: HomomorphicCommitment<F>> {
    pub verifier_key: PC::VerifierKey,
    pub fixed_oracles: Vec<FixedOracle<F, PC>>,
    pub index_info: IndexInfo<F>,

    pub zh_inverses_over_coset: Vec<F>,
}

impl<F: PrimeField, PC: HomomorphicCommitment<F>> Clone for VerifierKey<F, PC> {
    fn clone(&self) -> Self {
        Self {
            verifier_key: self.verifier_key.clone(),
            fixed_oracles: self.fixed_oracles.clone(),
            index_info: self.index_info.clone(),
            zh_inverses_over_coset: self.zh_inverses_over_coset.clone(),
        }
    }
}

pub struct ProverKey<F: PrimeField, PC: HomomorphicCommitment<F>> {
    pub vk: VerifierKey<F, PC>,
    pub committer_key: PC::CommitterKey,
    pub empty_rands_for_fixed: Vec<PC::Randomness>
}

impl<F: PrimeField, PC: HomomorphicCommitment<F>> ProverKey<F, PC> {
    pub fn from_ck_and_vk(ck: &PC::CommitterKey, vk: &VerifierKey<F, PC>) -> Self {
        Self {
            vk: vk.clone(), 
            committer_key: ck.clone(), 
            empty_rands_for_fixed: vec![PC::Randomness::empty(); vk.fixed_oracles.len()]
        }
    }
}

pub struct Proof<F: PrimeField, PC: HomomorphicCommitment<F>> {
    pub witness_commitments: Vec<PC::Commitment>,
    pub witness_evaluations: Vec<F>,
    pub quotient_chunk_commitments: Vec<PC::Commitment>,
    pub quotient_chunks_evaluations: Vec<F>,
    pub fixed_oracle_evals: Vec<F>,
    pub multiopen_proof: MultiOpenProof<F, PC>,
}
