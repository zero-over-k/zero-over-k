use ark_ff::PrimeField;
use ark_poly::{
    univariate::DensePolynomial, EvaluationDomain, GeneralEvaluationDomain,
};
use ark_poly_commit::{PCCommitment, PCRandomness, PolynomialCommitment};

use crate::{
    commitment::HomomorphicCommitment,
    error::Error,
    multiproof::Proof as MultiOpenProof,
    oracles::{fixed::FixedOracle, traits::Instantiable},
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

pub struct VerifierKey<F: PrimeField, PC: HomomorphicCommitment<F>> {
    pub verifier_key: PC::VerifierKey,
    pub selector_oracles: Vec<FixedOracle<F, PC>>,
    pub permutation_oracles: Vec<FixedOracle<F, PC>>,
    pub index_info: IndexInfo<F>,

    pub zh_inverses_over_coset: Vec<F>,
}

impl<F: PrimeField, PC: HomomorphicCommitment<F>> VerifierKey<F, PC> {
    pub fn handle_fixed_verifier(
        &mut self,
        ck: &PC::CommitterKey,
    ) -> Result<(), Error<PC::Error>> {
        let selector_labeled: Vec<_> = self
            .selector_oracles
            .iter()
            .map(|o| o.to_labeled())
            .collect();
        let (selector_commitments, _) =
            PC::commit(ck, selector_labeled.iter(), None)
                .map_err(Error::from_pc_err)?;

        for (selector, commitment) in
            self.selector_oracles.iter_mut().zip(selector_commitments)
        {
            selector.commitment = Some(commitment.commitment().clone());
            selector.evals_at_coset_of_extended_domain = None
        }

        let permutation_labeled: Vec<_> = self
            .permutation_oracles
            .iter()
            .map(|o| o.to_labeled())
            .collect();
        let (permutation_commitments, _) =
            PC::commit(ck, permutation_labeled.iter(), None)
                .map_err(Error::from_pc_err)?;

        for (sigma, commitment) in self
            .permutation_oracles
            .iter_mut()
            .zip(permutation_commitments)
        {
            sigma.commitment = Some(commitment.commitment().clone());
            sigma.evals_at_coset_of_extended_domain = None
        }

        Ok(())
    }

    pub fn handle_fixed_prover(
        &mut self,
        ck: &PC::CommitterKey,
    ) -> Result<(), Error<PC::Error>> {
        let selector_labeled: Vec<_> = self
            .selector_oracles
            .iter()
            .map(|o| o.to_labeled())
            .collect();
        let (selector_commitments, _) =
            PC::commit(ck, selector_labeled.iter(), None)
                .map_err(Error::from_pc_err)?;

        for (selector, commitment) in
            self.selector_oracles.iter_mut().zip(selector_commitments)
        {
            selector.commitment = Some(commitment.commitment().clone());
            selector.evals_at_coset_of_extended_domain = Some(
                self.index_info
                    .extended_coset_domain
                    .coset_fft(&selector.polynomial()),
            )
        }

        let permutation_labeled: Vec<_> = self
            .permutation_oracles
            .iter()
            .map(|o| o.to_labeled())
            .collect();
        let (permutation_commitments, _) =
            PC::commit(ck, permutation_labeled.iter(), None)
                .map_err(Error::from_pc_err)?;

        for (sigma, commitment) in self
            .permutation_oracles
            .iter_mut()
            .zip(permutation_commitments)
        {
            sigma.commitment = Some(commitment.commitment().clone());
            sigma.evals_at_coset_of_extended_domain = Some(
                self.index_info
                    .extended_coset_domain
                    .coset_fft(&sigma.polynomial()),
            )
        }

        Ok(())
    }
}

impl<F: PrimeField, PC: HomomorphicCommitment<F>> Clone for VerifierKey<F, PC> {
    fn clone(&self) -> Self {
        Self {
            verifier_key: self.verifier_key.clone(),
            selector_oracles: self.selector_oracles.clone(),
            permutation_oracles: self.permutation_oracles.clone(),
            index_info: self.index_info.clone(),
            zh_inverses_over_coset: self.zh_inverses_over_coset.clone(),
        }
    }
}

pub struct ProverKey<F: PrimeField, PC: HomomorphicCommitment<F>> {
    pub vk: VerifierKey<F, PC>,
    pub committer_key: PC::CommitterKey,
    pub empty_rands_for_fixed: Vec<PC::Randomness>,
}

impl<F: PrimeField, PC: HomomorphicCommitment<F>> ProverKey<F, PC> {
    pub fn from_ck_and_vk(
        ck: &PC::CommitterKey,
        vk: &VerifierKey<F, PC>,
    ) -> Self {
        Self {
            vk: vk.clone(),
            committer_key: ck.clone(),
            empty_rands_for_fixed: vec![
                PC::Randomness::empty();
                vk.selector_oracles.len()
                    + vk.permutation_oracles.len()
            ],
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
