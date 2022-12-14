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
    vo::LookupVirtualOracle,
};

use ark_serialize::{
    CanonicalDeserialize, CanonicalSerialize, SerializationError,
};
use ark_std::io::{Read, Write};

pub type UniversalSRS<F, PC> =
    <PC as PolynomialCommitment<F, DensePolynomial<F>>>::UniversalParams;

#[derive(Clone)]
pub struct PermutationInfo<F: PrimeField> {
    /// Usable rows
    pub u: usize,
    /// Separators for different wires
    pub deltas: Vec<F>,
}

impl<F: PrimeField> PermutationInfo<F> {
    /// Returns empty PermutationInfo used when the permutation argument is not used.
    pub fn empty() -> Self {
        Self {
            u: 0usize,
            deltas: Vec::new(),
        }
    }
}

impl<F: PrimeField> PermutationInfo<F> {
    pub fn dummy() -> Self {
        Self {
            u: 0,
            deltas: vec![],
        }
    }
}

// TODO: rename from IndexInfo -> Index
// TODO: move u in index instead of permutation info
#[derive(Clone)]
pub struct Index<'a, F: PrimeField> {
    pub quotient_degree: usize,
    pub extended_coset_domain: GeneralEvaluationDomain<F>,
    pub permutation_argument: PermutationArgument<F>,
    pub lookups: Vec<&'a dyn LookupVirtualOracle<F>>,
    pub usable_rows: usize,
}

pub struct ProverPreprocessedInput<F: PrimeField, PC: HomomorphicCommitment<F>>
{
    pub fixed_oracles: Vec<FixedProverOracle<F>>,
    pub permutation_oracles: Vec<FixedProverOracle<F>>,
    pub table_oracles: Vec<FixedProverOracle<F>>,
    pub q_blind: FixedProverOracle<F>,
    pub empty_rands_for_fixed: Vec<PC::Randomness>,
}

impl<F: PrimeField, PC: HomomorphicCommitment<F>>
    ProverPreprocessedInput<F, PC>
{
    pub fn new(
        fixed_oracles: &[FixedProverOracle<F>],
        permutation_oracles: &[FixedProverOracle<F>],
        table_oracles: &[FixedProverOracle<F>],
        q_blind: &FixedProverOracle<F>,
        index_info: &Index<F>,
    ) -> Self {
        let fixed_oracles = &mut fixed_oracles.to_vec();
        let permutation_oracles = &mut permutation_oracles.to_vec();
        let table_oracles = &mut table_oracles.to_vec();

        for oracle in fixed_oracles.iter_mut() {
            oracle.compute_extended_evals(&index_info.extended_coset_domain);
        }

        for oracle in permutation_oracles.iter_mut() {
            oracle.compute_extended_evals(&index_info.extended_coset_domain);
        }

        for oracle in table_oracles.iter_mut() {
            oracle.compute_extended_evals(&index_info.extended_coset_domain);
        }

        let mut q_blind = q_blind.clone();
        q_blind.compute_extended_evals(&index_info.extended_coset_domain);

        Self {
            empty_rands_for_fixed: vec![
                PC::Randomness::empty();
                fixed_oracles.len()
                    + permutation_oracles.len()
                    + table_oracles.len()
                    + 1 // for q_blind
            ],
            fixed_oracles: fixed_oracles.to_vec(),
            permutation_oracles: permutation_oracles.to_vec(),
            table_oracles: table_oracles.to_vec(),
            q_blind,
        }
    }
}

pub struct VerifierPreprocessedInput<
    F: PrimeField,
    PC: HomomorphicCommitment<F>,
> {
    pub fixed_oracles: Vec<FixedVerifierOracle<F, PC>>,
    pub table_oracles: Vec<FixedVerifierOracle<F, PC>>,
    pub permutation_oracles: Vec<FixedVerifierOracle<F, PC>>,
    pub q_blind: FixedVerifierOracle<F, PC>,
}

impl<F: PrimeField, PC: HomomorphicCommitment<F>>
    VerifierPreprocessedInput<F, PC>
{
    /// Creates a new VerifierPreprocessedInput
    pub fn new(
        fixed_oracles: Vec<FixedVerifierOracle<F, PC>>,
        table_oracles: Vec<FixedVerifierOracle<F, PC>>,
        permutation_oracles: Vec<FixedVerifierOracle<F, PC>>,
        q_blind: FixedVerifierOracle<F, PC>,
    ) -> Self {
        Self {
            fixed_oracles,
            table_oracles,
            permutation_oracles,
            q_blind,
        }
    }

    /// Creates a new VerifierPreprocessedInput without blinders
    pub fn new_wo_blind(
        fixed_oracles: Vec<FixedVerifierOracle<F, PC>>,
        table_oracles: Vec<FixedVerifierOracle<F, PC>>,
        permutation_oracles: Vec<FixedVerifierOracle<F, PC>>,
    ) -> Self {
        let q_blind =
            FixedVerifierOracle::new("q_blind", Some(PC::zero_comm()));
        Self {
            fixed_oracles,
            table_oracles,
            permutation_oracles,
            q_blind,
        }
    }
}

impl<F: PrimeField, PC: HomomorphicCommitment<F>> Clone
    for VerifierPreprocessedInput<F, PC>
{
    fn clone(&self) -> Self {
        Self {
            fixed_oracles: self.fixed_oracles.clone(),
            table_oracles: self.table_oracles.clone(),
            permutation_oracles: self.permutation_oracles.clone(),
            q_blind: self.q_blind.clone(),
        }
    }
}

pub struct VerifierKey<'a, F: PrimeField, PC: HomomorphicCommitment<F>> {
    pub verifier_key: PC::VerifierKey,
    pub index_info: Index<'a, F>,
    pub zh_inverses_over_coset: Vec<F>,
}

impl<'a, F: PrimeField, PC: HomomorphicCommitment<F>> Clone
    for VerifierKey<'a, F, PC>
{
    fn clone(&self) -> Self {
        Self {
            verifier_key: self.verifier_key.clone(),
            index_info: self.index_info.clone(),
            zh_inverses_over_coset: self.zh_inverses_over_coset.clone(),
        }
    }
}

pub struct ProverKey<'a, F: PrimeField, PC: HomomorphicCommitment<F>> {
    pub vk: VerifierKey<'a, F, PC>,
    pub committer_key: PC::CommitterKey,
}

impl<'a, F: PrimeField, PC: HomomorphicCommitment<F>> ProverKey<'a, F, PC> {
    pub fn from_ck_and_vk(
        ck: &PC::CommitterKey,
        vk: &VerifierKey<'a, F, PC>,
    ) -> Self {
        Self {
            vk: vk.clone(),
            committer_key: ck.clone(),
        }
    }
}

#[derive(CanonicalSerialize, CanonicalDeserialize)]
pub struct Proof<F: PrimeField, PC: HomomorphicCommitment<F>> {
    // witness oracles
    pub witness_commitments: Vec<PC::Commitment>,
    pub witness_evals: Vec<F>,
    // fixed oracles
    pub fixed_oracle_evals: Vec<F>,
    pub table_oracle_evals: Vec<F>,
    pub permutation_oracle_evals: Vec<F>,
    pub q_blind_eval: F,
    // lookup oracles
    pub lookup_commitments: Vec<PC::Commitment>,
    pub lookup_z_commitments: Vec<PC::Commitment>,
    pub lookup_evals: Vec<F>,
    pub lookup_z_evals: Vec<F>,
    // permutation aggregation
    pub z_commitments: Vec<PC::Commitment>,
    pub z_evals: Vec<F>,

    // quotient
    pub quotient_chunk_commitments: Vec<PC::Commitment>,
    pub quotient_chunks_evals: Vec<F>,

    // multiproof
    pub multiopen_proof: MultiOpenProof<F, PC>,
}

impl<F: PrimeField, PC: HomomorphicCommitment<F>> Proof<F, PC> {
    pub fn info(&self) -> String {
        format!(
            "Proof stats: \n
            witness commitments: {}
            witness evals: {}

            fixed oracle evals: {}
            table oracle evals: {}
            permutation oracle evals {}
            q blind eval 1

            lookup commitments {}
            lookup evals {}

            lookup z commitments {}
            lookup z evals {}

            quotient chunk commitments: {}
            quotient chunks evals: {}

            z commitments: {}
            z evals {}

            MultiOpenProof:
                q_evals: {}
                f_commit: 1
                opening_proof: 1,
            ",
            // witness
            self.witness_commitments.len(),
            self.witness_evals.len(),
            // fixed
            self.fixed_oracle_evals.len(),
            self.table_oracle_evals.len(),
            self.permutation_oracle_evals.len(),
            // lookups
            self.lookup_commitments.len(),
            self.lookup_evals.len(),
            self.lookup_z_commitments.len(),
            self.lookup_z_evals.len(),
            // quotient
            self.quotient_chunk_commitments.len(),
            self.quotient_chunks_evals.len(),
            // permutation agg polys
            self.z_commitments.len(),
            self.z_evals.len(),
            // multiopen
            self.multiopen_proof.q_evals.len()
        )
    }

    pub fn cumulative_info(&self) -> String {
        let num_of_commitments = self.witness_commitments.len()
            + self.lookup_commitments.len()
            + self.lookup_z_commitments.len()
            + self.quotient_chunk_commitments.len()
            + self.z_commitments.len()
            + 1; // + 1 for f commitment in multiopen
        let num_of_field_elements =
            // witness
            self.witness_evals.len()
            //fixed
            + self.fixed_oracle_evals.len()
            + self.table_oracle_evals.len()
            + self.permutation_oracle_evals.len()
            + 1 // q_blind
            //lookups
            + self.lookup_evals.len()
            + self.lookup_z_evals.len()
            // quotient
            + self.quotient_chunks_evals.len()
            // permutation agg polys
            + self.z_evals.len()
            // multiopen
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
    }
}
