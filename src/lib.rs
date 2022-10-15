use std::cmp::max;
use std::collections::{BTreeMap, BTreeSet};
use std::iter::{self, successors};
use std::marker::PhantomData;
use std::option::Iter;

use ark_ff::{to_bytes, PrimeField};
use ark_poly::univariate::DensePolynomial;
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain, Polynomial};
use ark_poly_commit::{
    LabeledPolynomial, PCCommitterKey, PCRandomness, PCUniversalParams,
};
use digest::generic_array::typenum::Quot;
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

use crate::iop::prover;
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

    /*
        We want to support both Plonkish like zero over K checks, where each gate is separated with selector, ex: (q_1, gate_1), (q_2, gate_2),
        and also arbitrary polynomial constraints, (ex. https://eprint.iacr.org/2021/1342.pdf look at proof of functional relation)
        where there is no concept of selector.

        There are multiple ways of how to blind some oracles.

        1. In Plonkish like style we can reserve some t rows for blinding and simply when constructing vanishing argument all selectors
        are zero at that t rows.

        2. When there are no selectors we can still use some t rows for blinding, but now instead of checking that something vanishes on

        zH = X^n - 1, we can check that it vanishes on zH = (X^n - 1) / prod{i in last [t]} (x - w_i)
    */
    pub fn index(
        ck: &PC::CommitterKey,
        vk: &PC::VerifierKey,
        vos: &[impl VirtualOracle<F>],
        witness_oracles: &mut [impl ConcreteOracle<F>],
        instance_oracles: &mut [InstanceOracle<F>],
        fixed_oracles: &mut [FixedOracle<F, PC>],
        domain: GeneralEvaluationDomain<F>,
        zH: DensePolynomial<F>,
    ) -> Result<VerifierKey<F, PC>, Error<PC::Error>> {
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
        let fixed_oracles_mapping: BTreeMap<String, usize> = fixed_oracles
            .iter()
            .enumerate()
            .map(|(i, oracle)| (oracle.get_label(), i))
            .collect();

        let domain_size = domain.size();
        let mut max_degree = 0;
        for vo in vos {
            let vo_degree =
                vo.get_expression().degree(&|query| {
                    match query.oracle_type {
                        OracleType::Witness => {
                            match witness_oracles_mapping.get(&query.label) {
                                Some(index) => witness_oracles[*index]
                                    .get_degree(domain_size),
                                None => panic!(
                                    "Witness oracle with label {} not found",
                                    query.label
                                ), //TODO: Introduce new Error here,
                            }
                        }
                        OracleType::Instance => {
                            match instance_oracles_mapping.get(&query.label) {
                                Some(index) => instance_oracles[*index]
                                    .get_degree(domain_size),
                                None => panic!(
                                    "Instance oracle with label {} not found",
                                    query.label
                                ), //TODO: Introduce new Error here,
                            }
                        }
                        OracleType::Fixed => {
                            match fixed_oracles_mapping.get(&query.label) {
                                Some(index) => fixed_oracles[*index]
                                    .get_degree(domain_size),
                                None => panic!(
                                    "Fixed oracle with label {} not found",
                                    query.label
                                ), //TODO: Introduce new Error here,
                            }
                        }
                    }
                });
            max_degree = max(max_degree, vo_degree);
        }

        let quotient_degree = max_degree - zH.degree();
        let extended_coset_domain =
            GeneralEvaluationDomain::<F>::new(quotient_degree).unwrap();

        /*
            Consider case when simple mul over whole domain is being checked: a * b - c = 0 and zH = X^n - 1,
            extended_coset_domain will be exactly domain and zH.coset_fft() will not work since zH.degree() = 16 > 15
        */
        let vanish_dense: DensePolynomial<F> =
            domain.vanishing_polynomial().into();
        let zh_inverses_over_coset = if vanish_dense == zH
            && domain_size == extended_coset_domain.size()
        {
            let zh_eval = domain
                .evaluate_vanishing_polynomial(F::multiplicative_generator())
                .inverse()
                .unwrap();
            iter::repeat(zh_eval).take(domain_size).collect()
        } else if vanish_dense == zH {
            // extended_coset_domain must be bigger then original domain
            let mut zh_evals = compute_vanishing_poly_over_coset(
                extended_coset_domain,
                domain_size as u64,
            );
            ark_ff::batch_inversion(&mut zh_evals);
            zh_evals
        } else {
            let mut zh_evals = extended_coset_domain.coset_fft(&zH);
            ark_ff::batch_inversion(&mut zh_evals);
            zh_evals
        };

        // assign queries to concrete oracles
        for vo in vos {
            for query in vo.get_queries() {
                match query.oracle_type {
                    OracleType::Witness => {
                        match witness_oracles_mapping.get(&query.label) {
                            Some(index) => witness_oracles[*index]
                                .register_rotation(query.rotation),
                            None => panic!(
                                "Witness oracle with label add_label not found"
                            ), //TODO: Introduce new Error here,
                        }
                    }
                    OracleType::Instance => {
                        match instance_oracles_mapping.get(&query.label) {
                            Some(index) => instance_oracles[*index].register_rotation(query.rotation),
                            None => panic!("Instance oracle with label add_label not found") //TODO: Introduce new Error here,
                        }
                    }
                    OracleType::Fixed => {
                        match fixed_oracles_mapping.get(&query.label) {
                            Some(index) => fixed_oracles[*index]
                                .register_rotation(query.rotation),
                            None => panic!(
                                "Fixed oracle with label add_label not found"
                            ), //TODO: Introduce new Error here,
                        }
                    }
                }
            }
        }

        let fixed_labeled: Vec<_> =
            fixed_oracles.iter().map(|o| o.to_labeled()).collect();
        let (fixed_commitments, _) = PC::commit(ck, fixed_labeled.iter(), None)
            .map_err(Error::from_pc_err)?;

        //TODO: verifier should not keep just fixed commitments while prover can keep polys&commitments&evals
        for (fixed, commitment) in
            fixed_oracles.iter_mut().zip(fixed_commitments)
        {
            fixed.commitment = Some(commitment.commitment().clone());
            fixed.evals_at_coset_of_extended_domain =
                Some(extended_coset_domain.coset_fft(&fixed.polynomial()))
        }

        let index_info = IndexInfo {
            quotient_degree,
            extended_coset_domain,
        };
        Ok(VerifierKey {
            verifier_key: vk.clone(),
            fixed_oracles: fixed_oracles.to_vec(),
            index_info,
            zh_inverses_over_coset,
        })
    }

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
        vos: &[Box<&'a dyn VirtualOracle<F>>],
        domain_size: usize,
        vanishing_polynomial: &DensePolynomial<F>,
        zk_rng: &mut R,
    ) -> Result<Proof<F, PC>, Error<PC::Error>> {
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

        let mut fs_rng =
            FS::initialize(&to_bytes![&Self::PROTOCOL_NAME].unwrap()); // TODO: add &pk.vk, &public oracles to transcript

        // --------------------------------------------------------------------
        // First round

        let witness_oracles = PIOPforPolyIdentity::<F, PC>::prover_first_round(
            &mut prover_state,
            zk_rng,
        )?;
        let witness_oracles_labeled: Vec<
            LabeledPolynomial<F, DensePolynomial<F>>,
        > = witness_oracles
            .iter()
            .map(|oracle| oracle.to_labeled())
            .collect();

        let (witness_commitments, wtns_rands) = PC::commit(
            &pk.committer_key,
            &witness_oracles_labeled,
            Some(zk_rng),
        )
        .map_err(Error::from_pc_err)?;

        fs_rng.absorb(&to_bytes![witness_commitments].unwrap());

        let (verifier_first_msg, verifier_state) =
            PIOPforPolyIdentity::<F, PC>::verifier_first_round(
                verifier_init_state,
                &mut fs_rng,
            );
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Second round

        let quotient_chunk_oracles = PIOPforPolyIdentity::prover_second_round(
            &verifier_first_msg,
            &mut prover_state,
            &pk.vk.index_info, //TOOD: remove this arg
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

        let domain = GeneralEvaluationDomain::new(domain_size).unwrap();
        let omegas: Vec<F> = domain.elements().collect();
        let witness_query_set = PIOPforPolyIdentity::<F, PC>::get_query_set(
            &witness_oracles,
            verifier_second_msg.label,
            verifier_second_msg.xi,
            &omegas,
        );
        let fixed_query_set = PIOPforPolyIdentity::<F, PC>::get_query_set(
            &pk.vk.fixed_oracles,
            verifier_second_msg.label,
            verifier_second_msg.xi,
            &omegas,
        );

        let witness_evaluations: Vec<F> = evaluate_query_set(
            witness_oracles_labeled.iter(),
            &witness_query_set,
        )
        .iter()
        .map(|(_, eval)| *eval)
        .collect();

        let fixed_oracles_labeled: Vec<_> =
            pk.vk.fixed_oracles.iter().map(|o| o.to_labeled()).collect();

        let fixed_oracle_evals: Vec<F> =
            evaluate_query_set(&fixed_oracles_labeled, &fixed_query_set)
                .iter()
                .map(|(_, eval)| *eval)
                .collect();

        let quotient_chunks_evaluations: Vec<F> = quotient_chunk_oracles
            .iter()
            .map(|q_i| {
                q_i.query(&QueryContext::Challenge(verifier_second_msg.xi))
            })
            .collect();

        let mut evaluations = vec![];
        evaluations.extend_from_slice(&witness_evaluations);
        evaluations.extend_from_slice(&quotient_chunks_evaluations);
        evaluations.extend_from_slice(&fixed_oracle_evals);

        // Multiopen
        let mut oracles: Vec<&dyn Instantiable<F>> = witness_oracles
            .iter()
            .chain(quotient_chunk_oracles.iter())
            .map(|o| o as &dyn Instantiable<F>)
            .collect();
        let fixed_oracles: Vec<&dyn Instantiable<F>> = pk
            .vk
            .fixed_oracles
            .iter()
            .map(|o| o as &dyn Instantiable<F>)
            .collect();
        oracles.extend_from_slice(&fixed_oracles.as_slice());

        //TODO: move rands into vk
        let fixed_rands = iter::repeat(PC::Randomness::empty())
            .take(fixed_oracles.len())
            .collect::<Vec<PC::Randomness>>();
        let oracle_rands: Vec<PC::Randomness> = wtns_rands
            .iter()
            .chain(quotient_rands.iter())
            .chain(fixed_rands.iter())
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
            witness_evaluations,
            quotient_chunk_commitments: quotient_chunk_commitments
                .iter()
                .map(|c| c.commitment().clone())
                .collect(),
            quotient_chunks_evaluations,
            fixed_oracle_evals,
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
        vos: &[Box<&dyn VirtualOracle<F>>],
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
        let fixed_oracles_mapping: BTreeMap<String, usize> = vk
            .fixed_oracles
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
                    proof.quotient_chunks_evaluations[i],
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

        assert_eq!(query_set.len(), proof.witness_evaluations.len());

        let fixed_query_set = PIOPforPolyIdentity::<F, PC>::get_query_set(
            &vk.fixed_oracles,
            verifier_second_msg.label,
            verifier_second_msg.xi,
            &omegas,
        );

        assert_eq!(fixed_query_set.len(), proof.fixed_oracle_evals.len());

        for ((poly_label, (_, point)), &evaluation) in
            fixed_query_set.iter().zip(proof.fixed_oracle_evals.iter())
        {
            match fixed_oracles_mapping.get(poly_label) {
                Some(index) => vk.fixed_oracles[*index]
                    .register_eval_at_challenge(*point, evaluation),
                None => panic!("Missing poly: {}", poly_label),
            };
        }

        // map claimed evaluations with proper oracles
        for ((poly_label, (_, point)), &evaluation) in
            query_set.iter().zip(proof.witness_evaluations.iter())
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
                            match fixed_oracles_mapping.get(&query.label) {
                                Some(index) => vk.fixed_oracles[*index].query(&QueryContext::Challenge(challenge)),
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
        let fixed_oracles: Vec<&dyn CommittedOracle<F, PC>> = vk
            .fixed_oracles
            .iter()
            .map(|o| o as &dyn CommittedOracle<F, PC>)
            .collect();
        oracles.extend_from_slice(&fixed_oracles.as_slice());

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
