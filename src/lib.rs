use ark_ff::PrimeField;
use ark_poly::univariate::DensePolynomial;
use ark_poly_commit::PolynomialCommitment;

use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::rand::{Rng, RngCore};
use commitment::HomomorphicCommitment;
use data_structures::{
    ProverKey, ProverPreprocessedInput, UniversalSRS, VerifierKey,
    VerifierPreprocessedInput,
};
use error::Error;
use oracles::instance::{InstanceProverOracle, InstanceVerifierOracle};

use oracles::witness::{WitnessProverOracle, WitnessVerifierOracle};
use rng::FiatShamirRng;
use vo::VirtualOracle;

pub mod commitment;
pub mod data_structures;
pub mod error;
pub mod oracles;
pub mod piop;
pub mod rng;
mod util;
pub mod vo;

pub mod indexer;
#[allow(clippy::too_many_arguments)]
pub mod lookup;
mod mock_prover;
pub mod multiproof;
pub mod permutation;
mod turbo_plonk;

mod tests;

pub type PCKeys<F, PC> = (
    <PC as PolynomialCommitment<F, DensePolynomial<F>>>::CommitterKey,
    <PC as PolynomialCommitment<F, DensePolynomial<F>>>::VerifierKey,
);
pub trait Proof: CanonicalSerialize + CanonicalDeserialize {
    // /// Size in bytes
    // fn size_in_bytes(&self) -> usize;
    /// Basic information about the proof.
    fn info(&self) -> String;

    fn cumulative_info(&self) -> String;
}

pub trait PIL<F: PrimeField, PC: HomomorphicCommitment<F>, FS: FiatShamirRng> {
    type Proof: Proof;
    const PROTOCOL_NAME: &'static [u8];
    fn universal_setup<R: RngCore>(
        max_degree: usize,
        rng: &mut R,
    ) -> Result<UniversalSRS<F, PC>, Error<PC::Error>>;

    fn prepare_keys(
        srs: &UniversalSRS<F, PC>,
    ) -> Result<PCKeys<F, PC>, Error<PC::Error>>;

    fn prove<'a, R: Rng>(
        pk: &ProverKey<F, PC>,
        preprocessed: &ProverPreprocessedInput<F, PC>,
        witness_oracles: &'a mut [WitnessProverOracle<F>],
        instance_oracles: &'a mut [InstanceProverOracle<F>],
        vos: &[&'a dyn VirtualOracle<F>], // TODO: this should be in index
        domain_size: usize,
        zk_rng: &mut R,
    ) -> Result<Self::Proof, Error<PC::Error>>;

    fn verify(
        vk: &VerifierKey<F, PC>,
        preprocessed: &mut VerifierPreprocessedInput<F, PC>,
        proof: Self::Proof,
        witness_oracles: &mut [WitnessVerifierOracle<F, PC>],
        instance_oracles: &mut [InstanceVerifierOracle<F>],
        vos: &[&dyn VirtualOracle<F>],
        domain_size: usize,
        vanishing_polynomial: &DensePolynomial<F>,
    ) -> Result<(), Error<PC::Error>>;
}
