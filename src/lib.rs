use std::collections::{BTreeMap, BTreeSet};
use std::iter::successors;
use std::marker::PhantomData;

use crate::concrete_oracle::{OracleType, QuerySetProvider};
use crate::error::Error;
use crate::vo::query::{Query, Rotation};
use ark_ff::{to_bytes, PrimeField, UniformRand, Zero};
use ark_poly::univariate::DensePolynomial;
use ark_poly::{
    evaluations, EvaluationDomain, GeneralEvaluationDomain, Polynomial,
};
use ark_poly_commit::LabeledPolynomial;
use ark_poly_commit::PCCommitterKey;
use ark_poly_commit::PCUniversalParams;
use ark_poly_commit::PolynomialCommitment;
use ark_poly_commit::QuerySet;
use ark_poly_commit::{evaluate_query_set, LabeledCommitment};
use ark_std::rand::Rng;
use ark_std::rand::RngCore;
use commitment::HomomorphicCommitment;
use concrete_oracle::CommittedConcreteOracle;
use concrete_oracle::InstantiableConcreteOracle;
use data_structures::Proof;
use data_structures::ProverKey;
use data_structures::UniversalSRS;
use data_structures::VerifierKey;
use iop::PIOPforPolyIdentity;
use multiproof::piop::{Multiopen, PIOP};
use rng::FiatShamirRng;
use vo::query::InstanceQuery;
use vo::query::WitnessQuery;
use vo::VirtualOracle;

pub mod commitment;
pub mod concrete_oracle;
mod data_structures;
pub mod error;
pub mod iop;
pub mod rng;
pub mod vo;

pub mod multiproof;

mod tests;

pub struct PIL<F: PrimeField, PC: HomomorphicCommitment<F>, FS: FiatShamirRng> {
    _field: PhantomData<F>,
    _pc: PhantomData<PC>,
    _fs: PhantomData<FS>,
}

impl<F, PC, FS> PIL<F, PC, FS>
where
    F: PrimeField,
    PC: HomomorphicCommitment<F>,
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
        let (committer_key, verifier_key) =
            PC::trim(&srs, srs.max_degree(), 0, None)
                .map_err(Error::from_pc_err)?;

        let vk = VerifierKey { verifier_key };

        let pk = ProverKey {
            vk: vk.clone(),
            committer_key,
        };

        Ok((pk, vk))
    }

    pub fn prove<R: Rng>(
        pk: &ProverKey<F, PC>,
        concrete_oracles: &[InstantiableConcreteOracle<F>],
        vos: &Vec<Box<dyn VirtualOracle<F>>>,
        domain_size: usize,
        vanishing_polynomial: &DensePolynomial<F>,
        zk_rng: &mut R,
    ) -> Result<Proof<F, PC>, Error<PC::Error>> {
        let mut prover_state = PIOPforPolyIdentity::init_prover(
            concrete_oracles,
            vos,
            domain_size,
            vanishing_polynomial,
        );

        let verifier_init_state = PIOPforPolyIdentity::init_verifier(
            domain_size,
            vanishing_polynomial,
        );

        let mut fs_rng =
            FS::initialize(&to_bytes![&Self::PROTOCOL_NAME].unwrap()); // TODO: add &pk.vk, &public oracles to transcript

        // --------------------------------------------------------------------
        // First round

        let witness_oracles =
            PIOPforPolyIdentity::prover_first_round(&mut prover_state, zk_rng)?;
        let witness_oracles_labeled: Vec<
            LabeledPolynomial<F, DensePolynomial<F>>,
        > = witness_oracles
            .iter()
            .map(|oracle| oracle.to_labeled())
            .collect();

        let (witness_commitments, _) =
            PC::commit(&pk.committer_key, &witness_oracles_labeled, None)
                .map_err(Error::from_pc_err)?;

        fs_rng.absorb(&to_bytes![witness_commitments].unwrap());

        let (verifier_first_msg, verifier_state) =
            PIOPforPolyIdentity::verifier_first_round(
                verifier_init_state,
                &mut fs_rng,
            );
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Second round

        let quotient_chunk_oracles = PIOPforPolyIdentity::prover_second_round(
            &verifier_first_msg,
            &mut prover_state,
            pk.committer_key.max_degree(),
        )?;

        let quotient_chunks_labeled: Vec<
            LabeledPolynomial<F, DensePolynomial<F>>,
        > = quotient_chunk_oracles
            .iter()
            .map(|oracle| oracle.to_labeled())
            .collect();

        let (quotient_chunk_commitments, _) =
            PC::commit(&pk.committer_key, &quotient_chunks_labeled, None)
                .map_err(Error::from_pc_err)?;

        fs_rng.absorb(&to_bytes![quotient_chunk_commitments].unwrap());

        let (verifier_second_msg, verifier_state) =
            PIOPforPolyIdentity::verifier_second_round(
                verifier_state,
                &mut fs_rng,
            );

        let domain = GeneralEvaluationDomain::new(domain_size).unwrap();
        let omegas: Vec<F> = domain.elements().collect();
        let query_set = PIOPforPolyIdentity::get_query_set(
            witness_oracles.iter(),
            verifier_second_msg.label,
            verifier_second_msg.xi,
            &omegas,
        );

        let witness_evaluations: Vec<F> =
            evaluate_query_set(witness_oracles_labeled.iter(), &query_set)
                .iter()
                .map(|(_, eval)| *eval)
                .collect();
        let quotient_chunks_evaluations: Vec<F> = quotient_chunk_oracles
            .iter()
            .map(|q_i| q_i.query_at_challenge(&verifier_second_msg.xi))
            .collect();

        let mut evaluations = vec![];
        evaluations.extend_from_slice(&witness_evaluations);
        evaluations.extend_from_slice(&quotient_chunks_evaluations);

        // Multiopen
        let oracles: Vec<InstantiableConcreteOracle<F>> = witness_oracles
            .iter()
            .chain(quotient_chunk_oracles.iter())
            .map(|oracle| oracle.clone())
            .collect();
        let multiopen_proof = Multiopen::<F, PC, FS>::prove(
            &pk.committer_key,
            &oracles,
            verifier_second_msg.xi,
            domain_size,
            &mut fs_rng,
        )
        .map_err(Error::from_multiproof_err)?;

        let proof = Proof {
            witness_commitments: witness_commitments
                .iter()
                .map(|c| c.commitment().clone())
                .collect(),
            witness_evaluations,
            quotient_chunk_commitments: quotient_chunk_commitments
                .iter()
                .map(|c| c.commitment().clone())
                .collect(),
            quotient_chunks_evaluations,
            multiopen_proof,
        };

        Ok(proof)
    }

    pub fn verify<R: Rng>(
        vk: &VerifierKey<F, PC>,
        proof: Proof<F, PC>,
        witness_oracles: &mut [CommittedConcreteOracle<F, PC>],
        instance_oracles: &mut [InstantiableConcreteOracle<F>],
        vos: &Vec<Box<dyn VirtualOracle<F>>>,
        domain_size: usize,
        vanishing_polynomial: &DensePolynomial<F>,
        srs_size: usize,
        zk_rng: &mut R,
    ) -> Result<(), Error<PC::Error>> {
        let verifier_init_state = PIOPforPolyIdentity::init_verifier(
            domain_size,
            vanishing_polynomial,
        );

        let mut fs_rng =
            FS::initialize(&to_bytes![&Self::PROTOCOL_NAME].unwrap()); // TODO: add &pk.vk, &public oracles to transcript

        let wtns_queries: BTreeSet<WitnessQuery> = vos
            .iter()
            .map(|vo| vo.get_wtns_queries())
            .flatten()
            .map(|query| query.clone())
            .map(|wtns_query| wtns_query.clone())
            .collect();

        let instance_queries: BTreeSet<InstanceQuery> = vos
            .iter()
            .map(|vo| vo.get_instance_queries())
            .flatten()
            .map(|query| query.clone())
            .map(|instance_query| instance_query.clone())
            .collect();

        // 2. Assign rotations to matching concrete oracles
        for query in &wtns_queries {
            if query.index >= witness_oracles.len() {
                return Err(Error::IndexTooLarge);
            }

            witness_oracles[query.index]
                .register_rotation(query.rotation.clone());
        }

        for query in &instance_queries {
            if query.index >= instance_oracles.len() {
                return Err(Error::IndexTooLarge);
            }

            instance_oracles[query.index]
                .register_rotation(query.rotation.clone());
        }

        let wtns_degree_fn = |query: &WitnessQuery| {
            witness_oracles[query.index].get_degree(domain_size)
        };

        let instance_degree_fn = |query: &InstanceQuery| {
            instance_oracles[query.index].get_degree(domain_size)
        };

        let mut max_degree = 0;
        for vo in vos {
            let vo_degree = vo
                .get_expression()
                .degree(&wtns_degree_fn, &instance_degree_fn);

            max_degree = std::cmp::max(max_degree, vo_degree);
        }

        let quotient_degree = max_degree - vanishing_polynomial.degree();

        let num_of_quotient_chunks = quotient_degree / srs_size
            + if quotient_degree % srs_size != 0 {
                1
            } else {
                0
            };

        if num_of_quotient_chunks != proof.quotient_chunk_commitments.len()
            || num_of_quotient_chunks != proof.quotient_chunks_evaluations.len()
        {
            return Err(Error::WrongNumberOfChunks);
        }

        // --------------------------------------------------------------------
        // First round

        fs_rng.absorb(&to_bytes![&proof.witness_commitments].unwrap());

        let (verifier_first_msg, verifier_state) =
            PIOPforPolyIdentity::verifier_first_round(
                verifier_init_state,
                &mut fs_rng,
            );

        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Second round

        fs_rng.absorb(&to_bytes![&proof.quotient_chunk_commitments].unwrap());

        let (verifier_second_msg, verifier_state) =
            PIOPforPolyIdentity::verifier_second_round(
                verifier_state,
                &mut fs_rng,
            );

        // --------------------------------------------------------------------

        for (witness_oracle, commitment) in witness_oracles
            .iter_mut()
            .zip(proof.witness_commitments.iter())
        {
            // TODO: we should consider doing this with storing ref to commitment but proof lifetime is causing some error
            witness_oracle.register_commitment(commitment.clone());
        }

        let quotient_chunk_oracles =
            (0..num_of_quotient_chunks).map(|i| CommittedConcreteOracle {
                label: format!("quotient_chunk_{}", i).to_string(),
                queried_rotations: BTreeSet::from([Rotation::curr()]),
                should_mask: false,
                evals_at_challenges: BTreeMap::from([(
                    verifier_second_msg.xi,
                    proof.quotient_chunks_evaluations[i],
                )]),
                commitment: Some(proof.quotient_chunk_commitments[i].clone()),
            });

        let domain = GeneralEvaluationDomain::new(domain_size).unwrap();
        let omegas: Vec<F> = domain.elements().collect();
        let query_set = PIOPforPolyIdentity::get_query_set(
            witness_oracles.iter(),
            verifier_second_msg.label,
            verifier_second_msg.xi,
            &omegas,
        );

        assert_eq!(query_set.len(), proof.witness_evaluations.len());

        let witness_label_index_mapping = witness_oracles
            .iter()
            .enumerate()
            .map(|(i, oracle)| (oracle.label.clone(), i))
            .collect::<BTreeMap<String, usize>>();

        // map claimed evaluations with proper oracles
        for ((poly_label, (_, point)), &evaluation) in
            query_set.iter().zip(proof.witness_evaluations.iter())
        {
            match witness_label_index_mapping.get(poly_label) {
                Some(index) => witness_oracles[*index]
                    .register_eval_at_challenge(*point, evaluation),
                None => panic!("Missing poly: {}", poly_label),
            };
        }

        let powers_of_alpha: Vec<F> = successors(Some(F::one()), |alpha_i| {
            Some(*alpha_i * verifier_first_msg.alpha)
        })
        .take(vos.len())
        .collect();

        let mut quotient_eval = F::zero();
        for (vo_index, vo) in vos.iter().enumerate() {
            let vo_evaluation = vo.get_expression().evaluate(
                &|x: F| x,
                &|query: &WitnessQuery| {
                    let oracle = &witness_oracles[query.get_index()];
                    let challenge = query.rotation.compute_evaluation_point(
                        verifier_second_msg.xi,
                        &omegas,
                    );
                    oracle.query_at_challenge(&challenge)
                },
                &|query: &InstanceQuery| {
                    let oracle = &instance_oracles[query.get_index()];
                    let challenge = query.rotation.compute_evaluation_point(
                        verifier_second_msg.xi,
                        &omegas,
                    );
                    oracle.query_at_challenge(&challenge)
                },
                &|x: F| -x,
                &|x: F, y: F| x + y,
                &|x: F, y: F| x * y,
                &|x: F, y: F| x * y,
            );

            quotient_eval += powers_of_alpha[vo_index] * vo_evaluation;
        }

        let x_n = verifier_second_msg.xi.pow([srs_size as u64, 0, 0, 0]);
        let powers_of_x: Vec<F> =
            successors(Some(F::one()), |x_i| Some(*x_i * x_n))
                .take(num_of_quotient_chunks)
                .collect();

        let mut t_part = F::zero();
        for (&x_i, t_i) in
            powers_of_x.iter().zip(quotient_chunk_oracles.clone())
        {
            t_part += x_i * t_i.query_at_challenge(&verifier_second_msg.xi);
        }

        t_part *= vanishing_polynomial.evaluate(&verifier_second_msg.xi);

        quotient_eval -= t_part;

        if quotient_eval != F::zero() {
            return Err(Error::QuotientNotZero);
        }

        let oracles: Vec<_> = witness_oracles
            .iter()
            .map(|oracle| oracle.clone())
            .chain(quotient_chunk_oracles)
            .collect();
        let res = Multiopen::<F, PC, FS>::verify(
            &vk.verifier_key,
            proof.multiopen_proof,
            &oracles,
            verifier_second_msg.xi,
            domain_size,
            &mut fs_rng,
        )
        .map_err(Error::from_multiproof_err)?;
        
        Ok(res)
    }
}
