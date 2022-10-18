use ark_ff::PrimeField;
use ark_poly::{
    univariate::DensePolynomial, EvaluationDomain, GeneralEvaluationDomain,
};
use ark_poly_commit::{
    LabeledCommitment, LabeledPolynomial, PCCommitment, PCRandomness,
    PolynomialCommitment,
};

use crate::{
    commitment::HomomorphicCommitment,
    error::Error,
    // error::Error,
    multiproof::Proof as MultiOpenProof,
    oracles::{
        fixed::{FixedProverOracle, FixedVerifierOracle},
        traits::Instantiable,
    },
};

use ark_serialize::{
    CanonicalDeserialize, CanonicalSerialize, SerializationError,
};
use ark_std::io::{Read, Write};

pub type UniversalSRS<F, PC> =
    <PC as PolynomialCommitment<F, DensePolynomial<F>>>::UniversalParams;

#[derive(Clone)]
pub struct IndexInfo<F: PrimeField> {
    pub quotient_degree: usize,
    pub extended_coset_domain: GeneralEvaluationDomain<F>,
}

pub struct ProverPreprocessedInput<F: PrimeField, PC: HomomorphicCommitment<F>>
{
    pub fixed_oracles: Vec<FixedProverOracle<F>>,
    pub permutation_oracles: Vec<FixedProverOracle<F>>,
    pub empty_rands_for_fixed: Vec<PC::Randomness>,
}

impl<F: PrimeField, PC: HomomorphicCommitment<F>>
    ProverPreprocessedInput<F, PC>
{
    pub fn from_evals_and_domains(
        selector_oracle_evals: &Vec<Vec<F>>,
        permutation_oracle_evals: &Vec<Vec<F>>,
        domain: &GeneralEvaluationDomain<F>,
        extended_coset_domain: &GeneralEvaluationDomain<F>,
    ) -> Self {
        let fixed_oracles: Vec<FixedProverOracle<F>> = selector_oracle_evals
            .iter()
            .enumerate()
            .map(|(i, evals)| {
                FixedProverOracle::from_evals_and_domains(
                    format!("fixed_{}", i).into(),
                    evals,
                    domain,
                    extended_coset_domain,
                )
            })
            .collect();

        let permutation_oracles: Vec<FixedProverOracle<F>> =
            permutation_oracle_evals
                .iter()
                .enumerate()
                .map(|(i, evals)| {
                    FixedProverOracle::from_evals_and_domains(
                        format!("sigma_{}", i).into(),
                        evals,
                        domain,
                        extended_coset_domain,
                    )
                })
                .collect();

        Self {
            empty_rands_for_fixed: vec![
                PC::Randomness::empty();
                fixed_oracles.len()
                    + permutation_oracles.len()
            ],
            fixed_oracles,
            permutation_oracles,
        }
    }

    pub fn new(
        fixed_oracles: &Vec<FixedProverOracle<F>>,
        permutation_oracles: &Vec<FixedProverOracle<F>>,
        index_info: &IndexInfo<F>
    ) -> Self {
        let mut fixed_oracles = fixed_oracles.clone(); 
        let mut permutation_oracles = permutation_oracles.clone();

        for oracle in fixed_oracles.iter_mut() {
            oracle.compute_extended_evals(&index_info.extended_coset_domain);
        }

        for oracle in permutation_oracles.iter_mut() {
            oracle.compute_extended_evals(&index_info.extended_coset_domain);
        }
        Self {
            empty_rands_for_fixed: vec![
                PC::Randomness::empty();
                fixed_oracles.len()
                    + permutation_oracles.len()
            ],
            fixed_oracles,
            permutation_oracles,
        }
    }
}

pub struct PreprocessedCommitments<F: PrimeField, PC: HomomorphicCommitment<F>>
{
    pub(crate) fixed_commitments: Vec<LabeledCommitment<PC::Commitment>>,
    pub(crate) permutation_commitments: Vec<LabeledCommitment<PC::Commitment>>,
}

impl<F: PrimeField, PC: HomomorphicCommitment<F>>
    PreprocessedCommitments<F, PC>
{
    pub fn to_verifier_preprocessed(&self) -> VerifierPreprocessedInput<F, PC> {
        VerifierPreprocessedInput {
            fixed_oracles: self
                .fixed_commitments
                .iter()
                .map(|c| FixedVerifierOracle::from_labeled_commitment(c))
                .collect(),
            permutation_oracles: self
                .permutation_commitments
                .iter()
                .map(|c| FixedVerifierOracle::from_labeled_commitment(c))
                .collect(),
        }
    }
}

pub struct VerifierPreprocessedInput<
    F: PrimeField,
    PC: HomomorphicCommitment<F>,
> {
    pub fixed_oracles: Vec<FixedVerifierOracle<F, PC>>,
    pub permutation_oracles: Vec<FixedVerifierOracle<F, PC>>,
}

impl<F: PrimeField, PC: HomomorphicCommitment<F>> Clone
    for VerifierPreprocessedInput<F, PC>
{
    fn clone(&self) -> Self {
        Self {
            fixed_oracles: self.fixed_oracles.clone(),
            permutation_oracles: self.permutation_oracles.clone(),
        }
    }
}

impl<F: PrimeField, PC: HomomorphicCommitment<F>>
    VerifierPreprocessedInput<F, PC>
{
    pub fn from_polys(
        ck: &PC::CommitterKey,
        selector_oracles: Vec<DensePolynomial<F>>,
        permutation_oracles: Vec<DensePolynomial<F>>,
    ) -> Result<Self, Error<PC::Error>> {
        let selector_labeled: Vec<LabeledPolynomial<F, DensePolynomial<F>>> =
            selector_oracles
                .iter()
                .enumerate()
                .map(|(i, oracle)| {
                    LabeledPolynomial::new(
                        format!("fixed_{}", i).into(),
                        oracle.clone(),
                        None,
                        None,
                    )
                })
                .collect();

        let sigma_labeled: Vec<LabeledPolynomial<F, DensePolynomial<F>>> =
            permutation_oracles
                .iter()
                .enumerate()
                .map(|(i, oracle)| {
                    LabeledPolynomial::new(
                        format!("sigma_{}", i).into(),
                        oracle.clone(),
                        None,
                        None,
                    )
                })
                .collect();

        let (selector_commitments, _) =
            PC::commit(ck, selector_labeled.iter(), None)
                .map_err(Error::from_pc_err)?;

        let (permutation_commitments, _) =
            PC::commit(ck, sigma_labeled.iter(), None)
                .map_err(Error::from_pc_err)?;

        Ok(Self {
            fixed_oracles: selector_commitments
                .iter()
                .map(|c| FixedVerifierOracle::from_labeled_commitment(c))
                .collect(),
            permutation_oracles: permutation_commitments
                .iter()
                .map(|c| FixedVerifierOracle::from_labeled_commitment(c))
                .collect(),
        })
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
    pub selector_oracle_evals: Vec<F>,
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
            selector oracle evals: {}
            MultiOpenProof:
                q_evals: {}
                f_commit: 1
                opening_proof: 1,
            ",
            self.witness_commitments.len(),
            self.witness_evals.len(),
            self.quotient_chunk_commitments.len(),
            self.quotient_chunks_evals.len(),
            self.selector_oracle_evals.len(),
            self.multiopen_proof.q_evals.len()
        )
        .to_string()
    }

    pub fn cumulative_info(&self) -> String {
        let num_of_commitments = self.witness_commitments.len()
            + self.quotient_chunk_commitments.len()
            + 1; // + 1 for f commitment in multiopen
        let num_of_field_elements = self.witness_evals.len()
            + self.quotient_chunks_evals.len()
            + self.selector_oracle_evals.len()
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
