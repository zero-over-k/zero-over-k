use ark_ff::PrimeField;
use ark_poly::univariate::DensePolynomial;
use ark_poly_commit::PolynomialCommitment;

pub struct ProverKey<F: PrimeField, PC: PolynomialCommitment<F, DensePolynomial<F>>> {
    pub committer_key: PC::CommitterKey,
}
