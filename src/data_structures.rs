use ark_ff::PrimeField;
use ark_poly::{univariate::DensePolynomial, GeneralEvaluationDomain};
use ark_poly_commit::PolynomialCommitment;

use crate::{
    commitment::HomomorphicCommitment, multiproof::Proof as MultiOpenProof,
};

pub type UniversalSRS<F, PC> =
    <PC as PolynomialCommitment<F, DensePolynomial<F>>>::UniversalParams;

pub struct VerifierKey<
    F: PrimeField,
    PC: PolynomialCommitment<F, DensePolynomial<F>>,
> {
    pub verifier_key: PC::VerifierKey,
}

pub struct ProverKey<
    F: PrimeField,
    PC: PolynomialCommitment<F, DensePolynomial<F>>,
> {
    pub vk: VerifierKey<F, PC>,
    pub committer_key: PC::CommitterKey,
}

impl<F: PrimeField, PC: PolynomialCommitment<F, DensePolynomial<F>>> Clone
    for VerifierKey<F, PC>
{
    fn clone(&self) -> Self {
        Self {
            verifier_key: self.verifier_key.clone(),
        }
    }
}

pub struct IndexInfo<F: PrimeField> {
    pub quotient_degree: usize,
    pub extended_coset_domain_size: GeneralEvaluationDomain<F>,
}

pub struct Proof<F: PrimeField, PC: HomomorphicCommitment<F>> {
    pub witness_commitments: Vec<PC::Commitment>,
    pub witness_evaluations: Vec<F>,
    pub quotient_chunk_commitments: Vec<PC::Commitment>,
    pub quotient_chunks_evaluations: Vec<F>,
    pub multiopen_proof: MultiOpenProof<F, PC>,
}
