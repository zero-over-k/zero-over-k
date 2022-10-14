use std::cmp::max;
use std::collections::{BTreeMap, BTreeSet};
use std::iter::{self, successors};
use std::marker::PhantomData;


use ark_ff::{to_bytes, PrimeField};
use ark_poly::univariate::DensePolynomial;
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain, Polynomial};
use ark_poly_commit::{
    LabeledPolynomial, PCCommitterKey, PCRandomness, PCUniversalParams,
};

use error::Error;

use ark_poly_commit::evaluate_query_set;
use ark_std::rand::{Rng, RngCore};
use commitment::HomomorphicCommitment;
use data_structures::{IndexInfo, Proof, ProverKey, UniversalSRS, VerifierKey};
use iop::PIOPforPolyIdentity;
use multiproof::piop::Multiopen;
use oracles::fixed::FixedOracle;
use oracles::instance::InstanceOracle;
use oracles::query::QueryContext;
use oracles::traits::{ConcreteOracle, Instantiable};
use oracles::witness::{WitnessProverOracle, WitnessVerifierOracle};
use rng::FiatShamirRng;
use vo::VirtualOracle;


use crate::oracles::query::OracleType;
use crate::oracles::rotation::Rotation;
use crate::oracles::traits::CommittedOracle;
use crate::util::compute_vanishing_poly_over_coset;

pub mod commitment;
mod data_structures;
pub mod error;
pub mod iop;
pub mod oracles;
pub mod rng;
mod util;
pub mod vo;

pub mod indexer;
pub mod multiproof;
pub mod permutation;

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
    ) -> Result<(PC::CommitterKey, PC::VerifierKey), Error<PC::Error>> {
        let supported_hiding_bound = 1; // we need to blind oracles for multiproof and opening in x3
        let (committer_key, verifier_key) =
            PC::trim(&srs, srs.max_degree(), supported_hiding_bound, None)
                .map_err(Error::from_pc_err)?;

        Ok((committer_key, verifier_key))
    }

    pub fn prove<'a, R: Rng>(
        pk: &ProverKey<F, PC>,
        witness_oracles: &'a mut [WitnessProverOracle<F>],
        instance_oracles: &'a mut [InstanceOracle<F>],
        vos: &[&'a dyn VirtualOracle<F>],
        domain_size: usize,
        vanishing_polynomial: &DensePolynomial<F>,
        zk_rng: &mut R,
    ) -> Result<Proof<F, PC>, Error<PC::Error>> {
        let mut fs_rng =
            FS::initialize(&to_bytes![&Self::PROTOCOL_NAME].unwrap()); // TODO: add &pk.vk, &public oracles to transcript

        // compute extended evals of each oracle
        for oracle in witness_oracles.iter_mut() {
            oracle.compute_extended_evals(
                &pk.vk.index_info.extended_coset_domain,
            );
        }

        for oracle in instance_oracles.iter_mut() {
            oracle.compute_extended_evals(
                &pk.vk.index_info.extended_coset_domain,
            );
        }

        // get labeled polys of witness oracles
        let witness_oracles_labeled: Vec<
            LabeledPolynomial<F, DensePolynomial<F>>,
        > = witness_oracles
            .iter()
            .map(|oracle| oracle.to_labeled())
            .collect();

        // commit to witness oracles
        let (witness_commitments, wtns_rands) = PC::commit(
            &pk.committer_key,
            &witness_oracles_labeled,
            Some(zk_rng),
        )
        .map_err(Error::from_pc_err)?;

        fs_rng.absorb(&to_bytes![witness_commitments].unwrap());

        // begin PIOP
        let mut prover_state = PIOPforPolyIdentity::init_prover(
            witness_oracles,
            instance_oracles,
            vos,
            domain_size,
            vanishing_polynomial,
            &pk.vk,
        );

        let verifier_init_state = PIOPforPolyIdentity::<F, PC>::init_verifier(
            domain_size,
            vanishing_polynomial,
        );

        let (verifier_first_msg, verifier_state) =
            PIOPforPolyIdentity::<F, PC>::verifier_first_round(
                verifier_init_state,
                &mut fs_rng,
            );

        // --------------------------------------------------------------------
        // First round

        let quotient_chunk_oracles = PIOPforPolyIdentity::prover_first_round(
            &verifier_first_msg,
            &mut prover_state,
            &pk.vk,
        )?;

        let quotient_chunks_labeled: Vec<
            LabeledPolynomial<F, DensePolynomial<F>>,
        > = quotient_chunk_oracles
            .iter()
            .map(|oracle| oracle.to_labeled())
            .collect();

        let (quotient_chunk_commitments, quotient_rands) = PC::commit(
            &pk.committer_key,
            &quotient_chunks_labeled,
            Some(zk_rng),
        )
        .map_err(Error::from_pc_err)?;

        fs_rng.absorb(&to_bytes![quotient_chunk_commitments].unwrap());

        let (verifier_second_msg, _verifier_state) =
            PIOPforPolyIdentity::<F, PC>::verifier_second_round(
                verifier_state,
                &mut fs_rng,
            );
        // --------------------------------------------------------------------

        let domain = GeneralEvaluationDomain::new(domain_size).unwrap();
        let omegas: Vec<F> = domain.elements().collect();
        let witness_query_set = PIOPforPolyIdentity::<F, PC>::get_query_set(
            &witness_oracles,
            verifier_second_msg.label,
            verifier_second_msg.xi,
            &omegas,
        );
        let selector_query_set = PIOPforPolyIdentity::<F, PC>::get_query_set(
            &pk.vk.selector_oracles,
            verifier_second_msg.label,
            verifier_second_msg.xi,
            &omegas,
        );

        let witness_evals: Vec<F> = evaluate_query_set(
            witness_oracles_labeled.iter(),
            &witness_query_set,
        )
        .iter()
        .map(|(_, eval)| *eval)
        .collect();

        let selector_oracles_labeled: Vec<_> = pk
            .vk
            .selector_oracles
            .iter()
            .map(|o| o.to_labeled())
            .collect();

        let selector_oracle_evals: Vec<F> =
            evaluate_query_set(&selector_oracles_labeled, &selector_query_set)
                .iter()
                .map(|(_, eval)| *eval)
                .collect();

        let quotient_chunks_evals: Vec<F> = quotient_chunk_oracles
            .iter()
            .map(|q_i| {
                q_i.query(&QueryContext::Challenge(verifier_second_msg.xi))
            })
            .collect();

        // let mut evaluations = vec![];
        // evaluations.extend_from_slice(&witness_evaluations);
        // evaluations.extend_from_slice(&quotient_chunks_evaluations);
        // evaluations.extend_from_slice(&selector_oracle_evals);

        // Multiopen
        let mut oracles: Vec<&dyn Instantiable<F>> = witness_oracles
            .iter()
            .chain(quotient_chunk_oracles.iter())
            .map(|o| o as &dyn Instantiable<F>)
            .collect();
        let selector_oracles: Vec<&dyn Instantiable<F>> = pk
            .vk
            .selector_oracles
            .iter()
            .map(|o| o as &dyn Instantiable<F>)
            .collect();
        oracles.extend_from_slice(&selector_oracles.as_slice());

        let oracle_rands: Vec<PC::Randomness> = wtns_rands
            .iter()
            .chain(quotient_rands.iter())
            .chain(pk.empty_rands_for_fixed.iter())
            .map(|rand| rand.clone())
            .collect();

        let multiopen_proof = Multiopen::<F, PC, FS>::prove(
            &pk.committer_key,
            &oracles,
            &oracle_rands,
            verifier_second_msg.xi,
            domain_size,
            &mut fs_rng,
            zk_rng,
        )
        .map_err(Error::from_multiproof_err)?;

        let proof = Proof {
            witness_commitments: witness_commitments
                .iter()
                .map(|c| c.commitment().clone())
                .collect(),
            witness_evals,
            quotient_chunk_commitments: quotient_chunk_commitments
                .iter()
                .map(|c| c.commitment().clone())
                .collect(),
            quotient_chunks_evals,
            selector_oracle_evals,
            multiopen_proof,
        };

        /* BEGIN SANITY CHECK BEFORE INVOKING VERIFIER */
        // let powers_of_alpha: Vec<F> = successors(Some(F::one()), |alpha_i| {
        //     Some(*alpha_i * verifier_first_msg.alpha)
        // })
        // .take(vos.len())
        // .collect();

        // let mut quotient_eval = F::zero();
        // for (vo_index, vo) in vos.iter().enumerate() {
        //     let vo_evaluation = vo.get_expression().evaluate(
        //         &|x: F| x,
        //         &|query| {
        //             let challenge = query.rotation.compute_evaluation_point(
        //                 verifier_second_msg.xi,
        //                 &omegas,
        //             );
        //             match query.oracle_type {
        //                 OracleType::Witness => {
        //                     match prover_state.witness_oracles_mapping.get(&query.label) {
        //                         Some(index) => prover_state.witness_oracles[*index].query(&QueryContext::Challenge(challenge)),
        //                         None => panic!("Witness oracle with label add_label not found") //TODO: Introduce new Error here,
        //                     }
        //                 },
        //                 OracleType::Instance => {
        //                     match prover_state.instance_oracles_mapping.get(&query.label) {
        //                         Some(index) => prover_state.instance_oracles[*index].query(&QueryContext::Challenge(challenge)),
        //                         None => panic!("Instance oracle with label {} not found", query.label) //TODO: Introduce new Error here,
        //                     }
        //                 },
        //                 OracleType::Fixed => {
        //                     match prover_state.fixed_oracles_mapping.get(&query.label) {
        //                         Some(index) => pk.vk.fixed_oracles[*index].query(&QueryContext::Challenge(challenge)),
        //                         None => panic!("Fixed oracle with label add_label not found") //TODO: Introduce new Error here,
        //                     }
        //                 },
        //             }
        //         },
        //         &|x: F| -x,
        //         &|x: F, y: F| x + y,
        //         &|x: F, y: F| x * y,
        //         &|x: F, y: F| x * y,
        //     );

        //     quotient_eval += powers_of_alpha[vo_index] * vo_evaluation;
        // }

        // let x_n = verifier_second_msg.xi.pow([domain_size as u64, 0, 0, 0]);
        // let powers_of_x: Vec<F> =
        //     successors(Some(F::one()), |x_i| Some(*x_i * x_n))
        //         .take(quotient_chunk_oracles.len())
        //         .collect();

        // let mut t_part = F::zero();
        // for (&x_i, t_i) in
        //     powers_of_x.iter().zip(quotient_chunk_oracles.clone())
        // {
        //     t_part += x_i
        //         * t_i.query(&QueryContext::Challenge(verifier_second_msg.xi));
        // }

        // t_part *= vanishing_polynomial.evaluate(&verifier_second_msg.xi);

        // quotient_eval -= t_part;
        // assert_eq!(quotient_eval, F::zero());
        /* END SANITY CHECK BEFORE INVOKING VERIFIER */

        Ok(proof)
    }

    pub fn verify<R: Rng>(
        vk: &mut VerifierKey<F, PC>,
        proof: Proof<F, PC>,
        witness_oracles: &mut [WitnessVerifierOracle<F, PC>],
        instance_oracles: &mut [InstanceOracle<F>],
        vos: &[&dyn VirtualOracle<F>],
        domain_size: usize,
        vanishing_polynomial: &DensePolynomial<F>,
        _zk_rng: &mut R,
    ) -> Result<(), Error<PC::Error>> {
        let verifier_init_state = PIOPforPolyIdentity::<F, PC>::init_verifier(
            domain_size,
            vanishing_polynomial,
        );

        let mut fs_rng =
            FS::initialize(&to_bytes![&Self::PROTOCOL_NAME].unwrap()); // TODO: add &pk.vk, &public oracles to transcript, fixed evals

        let witness_oracles_mapping: BTreeMap<String, usize> = witness_oracles
            .iter()
            .enumerate()
            .map(|(i, oracle)| (oracle.get_label(), i))
            .collect();
        let instance_oracles_mapping: BTreeMap<String, usize> =
            instance_oracles
                .iter()
                .enumerate()
                .map(|(i, oracle)| (oracle.get_label(), i))
                .collect();
        let selector_oracles_mapping: BTreeMap<String, usize> = vk
            .selector_oracles
            .iter()
            .enumerate()
            .map(|(i, oracle)| (oracle.get_label(), i))
            .collect();

        let num_of_quotient_chunks = proof.quotient_chunk_commitments.len();
        // SKIP FOR NOW
        // let num_of_quotient_chunks =
        //     vk.index_info.quotient_degree.next_power_of_two() / domain_size;

        // if num_of_quotient_chunks != proof.quotient_chunk_commitments.len()
        //     || num_of_quotient_chunks != proof.quotient_chunks_evaluations.len()
        // {
        //     dbg!(
        //         num_of_quotient_chunks,
        //         proof.quotient_chunk_commitments.len(),
        //         proof.quotient_chunks_evaluations.len(),
        //     );
        //     return Err(Error::WrongNumberOfChunks);
        // }

        // --------------------------------------------------------------------
        // First round

        fs_rng.absorb(&to_bytes![&proof.witness_commitments].unwrap());

        let (verifier_first_msg, verifier_state) =
            PIOPforPolyIdentity::<F, PC>::verifier_first_round(
                verifier_init_state,
                &mut fs_rng,
            );

        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Second round

        fs_rng.absorb(&to_bytes![&proof.quotient_chunk_commitments].unwrap());

        let (verifier_second_msg, _verifier_state) =
            PIOPforPolyIdentity::<F, PC>::verifier_second_round(
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

        let quotient_chunk_oracles = (0..num_of_quotient_chunks)
            .map(|i| WitnessVerifierOracle {
                label: format!("quotient_chunk_{}", i).to_string(),
                queried_rotations: BTreeSet::from([Rotation::curr()]),
                should_mask: false,
                evals_at_challenges: BTreeMap::from([(
                    verifier_second_msg.xi,
                    proof.quotient_chunks_evals[i],
                )]),
                commitment: Some(proof.quotient_chunk_commitments[i].clone()),
            })
            .collect::<Vec<_>>();

        let domain = GeneralEvaluationDomain::new(domain_size).unwrap();
        let omegas: Vec<F> = domain.elements().collect();
        let query_set = PIOPforPolyIdentity::<F, PC>::get_query_set(
            witness_oracles,
            verifier_second_msg.label,
            verifier_second_msg.xi,
            &omegas,
        );

        assert_eq!(query_set.len(), proof.witness_evals.len());

        let selector_query_set = PIOPforPolyIdentity::<F, PC>::get_query_set(
            &vk.selector_oracles,
            verifier_second_msg.label,
            verifier_second_msg.xi,
            &omegas,
        );

        assert_eq!(selector_query_set.len(), proof.selector_oracle_evals.len());

        for ((poly_label, (_, point)), &evaluation) in selector_query_set
            .iter()
            .zip(proof.selector_oracle_evals.iter())
        {
            match selector_oracles_mapping.get(poly_label) {
                Some(index) => vk.selector_oracles[*index]
                    .register_eval_at_challenge(*point, evaluation),
                None => panic!("Missing poly: {}", poly_label),
            };
        }

        // map claimed evaluations with proper oracles
        for ((poly_label, (_, point)), &evaluation) in
            query_set.iter().zip(proof.witness_evals.iter())
        {
            match witness_oracles_mapping.get(poly_label) {
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
                &|query| {
                    let challenge = query.rotation.compute_evaluation_point(
                        verifier_second_msg.xi,
                        &omegas,
                    );
                    match query.oracle_type {
                        OracleType::Witness => {
                            match witness_oracles_mapping.get(&query.label) {
                                Some(index) => witness_oracles[*index].query(&QueryContext::Challenge(challenge)),
                                None => panic!("Witness oracle with label add_label not found") //TODO: Introduce new Error here,
                            }
                        },
                        OracleType::Instance => {
                            match instance_oracles_mapping.get(&query.label) {
                                Some(index) => instance_oracles[*index].query(&QueryContext::Challenge(challenge)),
                                None => panic!("Instance oracle with label {} not found", query.label) //TODO: Introduce new Error here,
                            }
                        },
                        OracleType::Fixed => {
                            match selector_oracles_mapping.get(&query.label) {
                                Some(index) => vk.selector_oracles[*index].query(&QueryContext::Challenge(challenge)),
                                None => panic!("Fixed oracle with label add_label not found") //TODO: Introduce new Error here,
                            }
                        },
                    }
                },
                &|x: F| -x,
                &|x: F, y: F| x + y,
                &|x: F, y: F| x * y,
                &|x: F, y: F| x * y,
            );

            quotient_eval += powers_of_alpha[vo_index] * vo_evaluation;
        }

        let x_n = verifier_second_msg.xi.pow([domain_size as u64, 0, 0, 0]);
        let powers_of_x: Vec<F> =
            successors(Some(F::one()), |x_i| Some(*x_i * x_n))
                .take(num_of_quotient_chunks)
                .collect();

        let mut t_part = F::zero();
        for (&x_i, t_i) in
            powers_of_x.iter().zip(quotient_chunk_oracles.clone())
        {
            t_part += x_i
                * t_i.query(&QueryContext::Challenge(verifier_second_msg.xi));
        }

        t_part *= vanishing_polynomial.evaluate(&verifier_second_msg.xi);

        quotient_eval -= t_part;

        if quotient_eval != F::zero() {
            return Err(Error::QuotientNotZero);
        }

        let mut oracles: Vec<&dyn CommittedOracle<F, PC>> = witness_oracles
            .iter()
            .chain(quotient_chunk_oracles.iter())
            .map(|a| a as &dyn CommittedOracle<F, PC>)
            .collect();
        let selector_oracles: Vec<&dyn CommittedOracle<F, PC>> = vk
            .selector_oracles
            .iter()
            .map(|o| o as &dyn CommittedOracle<F, PC>)
            .collect();
        oracles.extend_from_slice(&selector_oracles.as_slice());

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
