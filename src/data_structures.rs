use ark_ff::PrimeField;
use ark_poly::univariate::DensePolynomial;
use ark_poly_commit::PolynomialCommitment;

pub type UniversalSRS<F, PC> = <PC as PolynomialCommitment<F, DensePolynomial<F>>>::UniversalParams;

pub struct VerifierKey<F: PrimeField, PC: PolynomialCommitment<F, DensePolynomial<F>>> {
    pub verifier_key: PC::VerifierKey,
}

pub struct ProverKey<F: PrimeField, PC: PolynomialCommitment<F, DensePolynomial<F>>> {
    pub vk: VerifierKey<F, PC>,
    pub committer_key: PC::CommitterKey,
}

impl<F: PrimeField, PC: PolynomialCommitment<F, DensePolynomial<F>>> Clone for VerifierKey<F, PC> {
    fn clone(&self) -> Self {
        Self {
            verifier_key: self.verifier_key.clone(),
        }
    }
}

pub struct Proof<F: PrimeField, PC: PolynomialCommitment<F, DensePolynomial<F>>> {
    pub commitments: Vec<Vec<PC::Commitment>>,
    pub evaluations: Vec<F>,
    pub opening_proof: PC::BatchProof,
}
