use ark_ff::PrimeField;
use ark_poly::univariate::DensePolynomial;
use ark_poly_commit::PolynomialCommitment;

use ark_std::rand::{Rng, RngCore};
use commitment::HomomorphicCommitment;
use data_structures::{
    Proof, ProverKey, ProverPreprocessedInput, UniversalSRS, VerifierKey,
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
pub mod multiproof;
pub mod permutation;
mod turbo_plonk;

mod tests;

pub type PCKeys<F, PC> = (
    <PC as PolynomialCommitment<F, DensePolynomial<F>>>::CommitterKey,
    <PC as PolynomialCommitment<F, DensePolynomial<F>>>::VerifierKey,
);

pub trait PIL<F: PrimeField, PC: HomomorphicCommitment<F>, FS: FiatShamirRng> {
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
    ) -> Result<Proof<F, PC>, Error<PC::Error>>;

    fn verify(
        vk: &VerifierKey<F, PC>,
        preprocessed: &mut VerifierPreprocessedInput<F, PC>,
        proof: Proof<F, PC>,
        witness_oracles: &mut [WitnessVerifierOracle<F, PC>],
        instance_oracles: &mut [InstanceVerifierOracle<F>],
        vos: &[&dyn VirtualOracle<F>],
        domain_size: usize,
        vanishing_polynomial: &DensePolynomial<F>,
    ) -> Result<(), Error<PC::Error>>;
}
