use std::marker::PhantomData;

use crate::error::Error;
use ark_ff::{to_bytes, PrimeField, UniformRand};
use ark_poly::{univariate::DensePolynomial, EvaluationDomain, GeneralEvaluationDomain};
use ark_poly_commit::LabeledPolynomial;
use ark_poly_commit::PCCommitterKey;
use ark_poly_commit::PCUniversalParams;
use ark_poly_commit::PolynomialCommitment;
use ark_std::rand::Rng;
use ark_std::rand::RngCore;
use concrete_oracle::{OracleType, ProverConcreteOracle};
use data_structures::ProverKey;
use data_structures::UniversalSRS;
use data_structures::VerifierKey;
use iop::{prover::ProverState, IOPforPolyIdentity};
use rng::FiatShamirRng;
use vo::VirtualOracle;

pub mod concrete_oracle;
mod data_structures;
pub mod error;
pub mod iop;
pub mod rng;
pub mod vo;

mod tests;

pub struct PIL<F: PrimeField, PC: PolynomialCommitment<F, DensePolynomial<F>>, FS: FiatShamirRng> {
    _field: PhantomData<F>,
    _pc: PhantomData<PC>,
    _fs: PhantomData<FS>,
}

impl<F, PC, FS> PIL<F, PC, FS>
where
    F: PrimeField,
    PC: PolynomialCommitment<F, DensePolynomial<F>>,
    FS: FiatShamirRng,
{
    pub const PROTOCOL_NAME: &'static [u8] = b"PIL-0.0.1";

    pub fn universal_setup<R: RngCore>(
        max_degree: usize,
        rng: &mut R,
    ) -> Result<UniversalSRS<F, PC>, Error<PC::Error>> {
        let srs = PC::setup(max_degree, None, rng).map_err(Error::from_pc_err);
        srs
    }

    pub fn prepare_keys(
        srs: &UniversalSRS<F, PC>,
    ) -> Result<(ProverKey<F, PC>, VerifierKey<F, PC>), Error<PC::Error>> {
        // keep all params simple for now
        let (committer_key, verifier_key) = PC::trim(
            &srs,
            srs.max_degree(),
            0,
            None,
        )
        .map_err(Error::from_pc_err)?;

        let vk = VerifierKey {
            verifier_key
        };

        let pk = ProverKey {
            vk: vk.clone(),
            committer_key
        };

        Ok((pk, vk))
    }

    pub fn prove<R: Rng>(
        pk: &ProverKey<F, PC>,
        concrete_oracles: &[ProverConcreteOracle<F>],
        vos: &Vec<Box<dyn VirtualOracle<F>>>,
        domain_size: usize,
        vanishing_polynomial: &DensePolynomial<F>,
        zk_rng: &mut R,
    ) -> Result<(), Error<PC::Error>> {
        let mut prover_state = IOPforPolyIdentity::init_prover(
            concrete_oracles,
            vos,
            domain_size,
            vanishing_polynomial,
        );

        let verifier_init_state =
            IOPforPolyIdentity::init_verifier(domain_size, vanishing_polynomial);

        let mut fs_rng = FS::initialize(&to_bytes![&Self::PROTOCOL_NAME].unwrap()); // TODO: add &pk.vk, &public oracles to transcript

        // --------------------------------------------------------------------
        // First round

        let prover_first_oracles =
            IOPforPolyIdentity::prover_first_round(&mut prover_state, zk_rng)?;
        let first_oracles_labeled: Vec<LabeledPolynomial<F, DensePolynomial<F>>> =
            prover_first_oracles
                .iter()
                .map(|oracle| oracle.to_labeled())
                .collect();

        let (first_comms, first_comm_rands) =
            PC::commit(&pk.committer_key, &first_oracles_labeled, None)
                .map_err(Error::from_pc_err)?;

        fs_rng.absorb(&to_bytes![first_comms].unwrap());

        let (verifier_first_msg, verifier_state) =
            IOPforPolyIdentity::verifier_first_round(verifier_init_state, &mut fs_rng);
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Second round

        println!("prosla prva runda");


        let prover_second_oracles = IOPforPolyIdentity::prover_second_round(
            &verifier_first_msg,
            &mut prover_state,
            pk.committer_key.max_degree(),
        )?;

        let second_oracles_labeled: Vec<LabeledPolynomial<F, DensePolynomial<F>>> =
            prover_second_oracles
                .iter()
                .map(|oracle| oracle.to_labeled())
                .collect();

        let (second_comms, second_comm_rands) =
            PC::commit(&pk.committer_key, &second_oracles_labeled, None)
                .map_err(Error::from_pc_err)?;

        fs_rng.absorb(&to_bytes![second_comms].unwrap());

        let (verifier_second_msg, verifier_state) =
            IOPforPolyIdentity::verifier_second_round(verifier_state, &mut fs_rng);
        // --------------------------------------------------------------------

        println!("ovde");

        // Gather prover polynomials in one vector.
        let polynomials: Vec<_> = first_oracles_labeled
            .iter()
            .chain(second_oracles_labeled.iter())
            .collect();

        let commitments: Vec<_> = first_comms.iter().chain(second_comms.iter()).collect();

        // Gather commitment randomness together.
        let rands: Vec<PC::Randomness> = first_comm_rands
            .into_iter()
            .chain(second_comm_rands)
            .collect();

        // Compute the AHP verifier's query set.
        let query_set = IOPforPolyIdentity::get_query_set(
            &verifier_state,
            prover_first_oracles
                .iter()
                .chain(prover_second_oracles.iter()),
        );

        println!("query set: {:?}", query_set);

        // TODO: add evaluations in transcript
        let opening_challenge: F = u128::rand(&mut fs_rng).into();

        let opening_proof = PC::batch_open(
            &pk.committer_key,
            polynomials,
            commitments,
            &query_set,
            opening_challenge,
            &rands,
            Some(zk_rng),
        )
        .map_err(Error::from_pc_err)?;

        Ok(())
    }
}
