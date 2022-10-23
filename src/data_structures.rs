use ark_ff::PrimeField;
use ark_poly::{univariate::DensePolynomial, GeneralEvaluationDomain};
use ark_poly_commit::{PCRandomness, PolynomialCommitment};

use crate::{
    commitment::HomomorphicCommitment,
    // error::Error,
    multiproof::Proof as MultiOpenProof,
    oracles::{
        fixed::{FixedProverOracle, FixedVerifierOracle},
        traits::Instantiable,
    },
    permutation::PermutationArgument,
};

use ark_serialize::{
    CanonicalDeserialize, CanonicalSerialize, SerializationError,
};
use ark_std::io::{Read, Write};

pub type UniversalSRS<F, PC> =
    <PC as PolynomialCommitment<F, DensePolynomial<F>>>::UniversalParams;

#[derive(Clone)]
pub struct PermutationInfo<F: PrimeField> {
    pub u: usize,       // usable rows
    pub deltas: Vec<F>, // separators for different wires
}

impl<F: PrimeField> PermutationInfo<F> {
    pub fn dummy() -> Self {
        Self {
            u: 0,
            deltas: vec![],
        }
    }
}

#[derive(Clone)]
pub struct IndexInfo<F: PrimeField> {
    pub quotient_degree: usize,
    pub extended_coset_domain: GeneralEvaluationDomain<F>,
    pub permutation_argument: PermutationArgument<F>,
}

pub struct ProverPreprocessedInput<F: PrimeField, PC: HomomorphicCommitment<F>>
{
    pub fixed_oracles: Vec<FixedProverOracle<F>>,
    pub permutation_oracles: Vec<FixedProverOracle<F>>,
    pub q_blind: FixedProverOracle<F>,
    pub empty_rands_for_fixed: Vec<PC::Randomness>,
}

impl<F: PrimeField, PC: HomomorphicCommitment<F>>
    ProverPreprocessedInput<F, PC>
{
    pub fn new(
        fixed_oracles: &Vec<FixedProverOracle<F>>,
        permutation_oracles: &Vec<FixedProverOracle<F>>,
        q_blind: &FixedProverOracle<F>,
        index_info: &IndexInfo<F>,
    ) -> Self {
        let mut fixed_oracles = fixed_oracles.clone();
        let mut permutation_oracles = permutation_oracles.clone();

        for oracle in fixed_oracles.iter_mut() {
            oracle.compute_extended_evals(&index_info.extended_coset_domain);
        }

        for oracle in permutation_oracles.iter_mut() {
            oracle.compute_extended_evals(&index_info.extended_coset_domain);
        }

        let mut q_blind = q_blind.clone();
        q_blind.compute_extended_evals(&index_info.extended_coset_domain);

        Self {
            empty_rands_for_fixed: vec![
                PC::Randomness::empty();
                fixed_oracles.len()
                    + permutation_oracles.len()
                    + 1 // for q_blind
            ],
            fixed_oracles,
            permutation_oracles,
            q_blind,
        }
    }
}

pub struct VerifierPreprocessedInput<
    F: PrimeField,
    PC: HomomorphicCommitment<F>,
> {
    pub fixed_oracles: Vec<FixedVerifierOracle<F, PC>>,
    pub permutation_oracles: Vec<FixedVerifierOracle<F, PC>>,
    pub q_blind: FixedVerifierOracle<F, PC>,
}

impl<F: PrimeField, PC: HomomorphicCommitment<F>> Clone
    for VerifierPreprocessedInput<F, PC>
{
    fn clone(&self) -> Self {
        Self {
            fixed_oracles: self.fixed_oracles.clone(),
            permutation_oracles: self.permutation_oracles.clone(),
            q_blind: self.q_blind.clone(),
        }
    }
}
pub struct VerifierKey<F: PrimeField, PC: HomomorphicCommitment<F>> {
    pub verifier_key: PC::VerifierKey,
    pub index_info: IndexInfo<F>,
    pub zh_inverses_over_coset: Vec<F>,
}

impl<F: PrimeField, PC: HomomorphicCommitment<F>> Clone for VerifierKey<F, PC> {
    fn clone(&self) -> Self {
        Self {
            verifier_key: self.verifier_key.clone(),
            index_info: self.index_info.clone(),
            zh_inverses_over_coset: self.zh_inverses_over_coset.clone(),
        }
    }
}

pub struct ProverKey<F: PrimeField, PC: HomomorphicCommitment<F>> {
    pub vk: VerifierKey<F, PC>,
    pub committer_key: PC::CommitterKey,
}

impl<F: PrimeField, PC: HomomorphicCommitment<F>> ProverKey<F, PC> {
    pub fn from_ck_and_vk(
        ck: &PC::CommitterKey,
        vk: &VerifierKey<F, PC>,
    ) -> Self {
        Self {
            vk: vk.clone(),
            committer_key: ck.clone(),
        }
    }
}

#[derive(CanonicalSerialize, CanonicalDeserialize)]
pub struct Proof<F: PrimeField, PC: HomomorphicCommitment<F>> {
    pub witness_commitments: Vec<PC::Commitment>,
    pub witness_evals: Vec<F>,
    pub quotient_chunk_commitments: Vec<PC::Commitment>,
    pub quotient_chunks_evals: Vec<F>,
    pub fixed_oracle_evals: Vec<F>,
    pub z_commitments: Vec<PC::Commitment>,
    pub z_evals: Vec<F>,
    pub permutation_oracle_evals: Vec<F>,
    pub q_blind_eval: F,
    pub multiopen_proof: MultiOpenProof<F, PC>,
}

impl<F: PrimeField, PC: HomomorphicCommitment<F>> Proof<F, PC> {
    pub fn info(&self) -> String {
        format!(
            "Proof stats: \n
            witness commitments: {}
            witness evals: {}
            quotient chunk commitments: {}
            quotient chunks evals: {}
            fixed oracle evals: {}
            z commitments: {}
            z evals {}
            permutation oracle evals: {}
            q_blind_eval 1
            MultiOpenProof:
                q_evals: {}
                f_commit: 1
                opening_proof: 1,
            ",
            self.witness_commitments.len(),
            self.witness_evals.len(),
            self.quotient_chunk_commitments.len(),
            self.quotient_chunks_evals.len(),
            self.fixed_oracle_evals.len(),
            self.z_commitments.len(),
            self.z_evals.len(),
            self.permutation_oracle_evals.len(),
            self.multiopen_proof.q_evals.len()
        )
        .to_string()
    }

    pub fn cumulative_info(&self) -> String {
        let num_of_commitments = self.witness_commitments.len()
            + self.quotient_chunk_commitments.len()
            + self.z_commitments.len()
            + 1; // + 1 for f commitment in multiopen
        let num_of_field_elements = self.witness_evals.len()
            + self.quotient_chunks_evals.len()
            + self.fixed_oracle_evals.len()
            + self.z_evals.len()
            + self.permutation_oracle_evals.len()
            + 1 // q_blind
            + self.multiopen_proof.q_evals.len();

        format!(
            "
            Proof is consisted of: \n
            {} commitments
            {} field elements
            1 PC::Proof
            ",
            num_of_commitments, num_of_field_elements
        )
        .to_string()
    }
}
