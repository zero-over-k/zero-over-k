use std::collections::{BTreeMap, BTreeSet};
use std::iter::successors;
use std::marker::PhantomData;

use crate::concrete_oracle::{
    OracleType, Queriable, QueryContext, QueryPoint, QuerySetProvider,
};
use crate::error::Error;
use crate::vo::linearisation::{
    LinearisationInfo, LinearisationOracleQuery, LinearisationPolyCommitment,
    LinearisationQueriable, LinearisationQueryResponse,
};
use crate::vo::query::{Query, Rotation};
use ark_ff::{to_bytes, PrimeField, UniformRand, Zero};
use ark_poly::univariate::DensePolynomial;
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain, Polynomial};
use ark_poly_commit::LabeledCommitment;
use ark_poly_commit::LabeledPolynomial;
use ark_poly_commit::PCCommitterKey;
use ark_poly_commit::PCUniversalParams;
use ark_poly_commit::PolynomialCommitment;
use ark_poly_commit::QuerySet;
use ark_std::rand::Rng;
use ark_std::rand::RngCore;
use commitment::HomomorphicCommitment;
use concrete_oracle::ProverConcreteOracle;
use concrete_oracle::VerifierConcreteOracle;
use data_structures::Proof;
use data_structures::ProverKey;
use data_structures::UniversalSRS;
use data_structures::VerifierKey;
use iop::IOPforPolyIdentity;
use rng::FiatShamirRng;
use vo::query::InstanceQuery;
use vo::query::WitnessQuery;
use vo::{LinearisableVirtualOracle, VirtualOracle};

pub mod commitment;
pub mod concrete_oracle;
mod data_structures;
pub mod error;
pub mod iop;
pub mod rng;
pub mod vo;

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
        concrete_oracles: &[ProverConcreteOracle<F>],
        vos: &Vec<Box<dyn LinearisableVirtualOracle<F>>>,
        domain_size: usize,
        vanishing_polynomial: &DensePolynomial<F>,
        zk_rng: &mut R,
    ) -> Result<Proof<F, PC>, Error<PC::Error>> {
        let mut prover_state = IOPforPolyIdentity::init_prover(
            concrete_oracles,
            vos,
            domain_size,
            vanishing_polynomial,
        );

        let verifier_init_state = IOPforPolyIdentity::init_verifier(
            domain_size,
            vanishing_polynomial,
        );

        let mut fs_rng =
            FS::initialize(&to_bytes![&Self::PROTOCOL_NAME].unwrap()); // TODO: add &pk.vk, &public oracles to transcript

        // --------------------------------------------------------------------
        // First round

        let prover_first_oracles =
            IOPforPolyIdentity::prover_first_round(&mut prover_state, zk_rng)?;
        let first_oracles_labeled: Vec<
            LabeledPolynomial<F, DensePolynomial<F>>,
        > = prover_first_oracles
            .iter()
            .map(|oracle| oracle.to_labeled())
            .collect();

        let (first_comms, first_comm_rands) =
            PC::commit(&pk.committer_key, &first_oracles_labeled, None)
                .map_err(Error::from_pc_err)?;

        fs_rng.absorb(&to_bytes![first_comms].unwrap());

        let (verifier_first_msg, verifier_state) =
            IOPforPolyIdentity::verifier_first_round(
                verifier_init_state,
                &mut fs_rng,
            );
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Second round

        let prover_second_oracles = IOPforPolyIdentity::prover_second_round(
            &verifier_first_msg,
            &mut prover_state,
            pk.committer_key.max_degree(),
        )?;

        let second_oracles_labeled: Vec<
            LabeledPolynomial<F, DensePolynomial<F>>,
        > = prover_second_oracles
            .iter()
            .map(|oracle| oracle.to_labeled())
            .collect();

        let (second_comms, second_comm_rands) =
            PC::commit(&pk.committer_key, &second_oracles_labeled, None)
                .map_err(Error::from_pc_err)?;

        fs_rng.absorb(&to_bytes![second_comms].unwrap());

        let (verifier_second_msg, verifier_state) =
            IOPforPolyIdentity::verifier_second_round(
                verifier_state,
                &mut fs_rng,
            );
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Third round

        let prover_third_oracles = IOPforPolyIdentity::prover_third_round::<PC>(
            &verifier_first_msg,
            &verifier_second_msg,
            &mut prover_state,
            pk.committer_key.max_degree(),
        )?;
        let third_oracles_labeled: Vec<
            LabeledPolynomial<F, DensePolynomial<F>>,
        > = prover_third_oracles
            .iter()
            .map(|oracle| oracle.to_labeled())
            .collect();

        let (third_comms, third_comm_rands) =
            PC::commit(&pk.committer_key, &third_oracles_labeled, None)
                .map_err(Error::from_pc_err)?;

        fs_rng.absorb(&to_bytes![third_comms].unwrap());
        // --------------------------------------------------------------------

        // Gather prover polynomials in one vector.
        let polynomials: Vec<_> = first_oracles_labeled
            .iter()
            .chain(second_oracles_labeled.iter())
            .collect();

        let commitments: Vec<_> =
            first_comms.iter().chain(second_comms.iter()).collect();

        // Gather commitment randomness together.
        let rands: Vec<PC::Randomness> = first_comm_rands
            .into_iter()
            .chain(second_comm_rands)
            .collect();

        // BEGIN QUERY SET
        let domain = GeneralEvaluationDomain::<F>::new(domain_size).unwrap();
        let omegas = domain.elements().collect();
        let mut query_set = QuerySet::<F>::new();
        for vo in vos {
            let q_set_i = vo
                .get_linearisation_expression()
                .compute_linearisation_query_set(
                    &|query: &LinearisationOracleQuery| {
                        let oracle = match query.oracle_type {
                            concrete_oracle::OracleType::Witness => {
                                &prover_state.witness_oracles[query.index]
                            }
                            concrete_oracle::OracleType::Instance => {
                                // Do not commit&open to instance
                                return vec![];
                            }
                        };

                        let point_info = oracle.get_point_info(
                            verifier_second_msg.label,
                            verifier_second_msg.xi,
                            &omegas,
                            query.rotation,
                        );
                        vec![(oracle.label.clone(), point_info)]
                    },
                );

            query_set.extend(q_set_i);
        }

        // Append quotient chunks queries to query_set
        for chunk in &prover_second_oracles {
            let point_info = chunk.get_point_info(
                verifier_second_msg.label,
                verifier_second_msg.xi,
                &omegas,
                Rotation::curr(),
            );
            query_set.insert((chunk.label.clone(), point_info));
        }
        // END QUERY SET

        println!("query set: {:?}", query_set);
        // println!("---------------------------");

        let evals = ark_poly_commit::evaluate_query_set(
            polynomials.clone(),
            &query_set,
        );
        // println!("evaluations: {:?}", evals);
        // println!("---------------------------");

        // Make sure that BTreeMap is sorted by poly_label, point_value so that verifier can deterministically reconstruct evals from commitments and query set
        // BEGIN SANITY CHECK
        // let mut evals_vec: Vec<(String, F, F)> = evals.iter().map(|((poly_label, point), &evaluation)| (poly_label.clone(), point.clone(), evaluation)).collect();
        // let mut evals_vec_copy: Vec<(String, F, F)> = evals.iter().map(|((poly_label, point), &evaluation)| (poly_label.clone(), point.clone(), evaluation)).collect();
        // evals_vec.sort_unstable_by_key(|item| (item.0.clone(), item.1));
        // assert_eq!(evals_vec, evals_vec_copy);
        // END SANITY CHECK

        let evals = evals.into_iter().map(|item| item.1).collect::<Vec<F>>();
        fs_rng.absorb(&evals);

        // TODO: add evaluations in transcript
        let opening_challenge: F = u128::rand(&mut fs_rng).into();

        let opening_proof = PC::batch_open(
            &pk.committer_key,
            polynomials,
            commitments.clone(),
            &query_set,
            opening_challenge,
            &rands,
            Some(zk_rng),
        )
        .map_err(Error::from_pc_err)?;

        let commitments = vec![
            first_comms.iter().map(|c| c.commitment().clone()).collect(),
            second_comms
                .iter()
                .map(|c| c.commitment().clone())
                .collect(),
        ];

        let proof = Proof {
            commitments,
            evaluations: evals,
            opening_proof,
        };

        Ok(proof)
    }

    pub fn verify<R: Rng>(
        vk: &VerifierKey<F, PC>,
        proof: Proof<F, PC>,
        witness_oracles: &mut [VerifierConcreteOracle<F, PC>],
        instance_oracles: &mut [ProverConcreteOracle<F>],
        vos: &Vec<Box<dyn LinearisableVirtualOracle<F>>>,
        domain_size: usize,
        vanishing_polynomial: &DensePolynomial<F>,
        srs_size: usize,
        zk_rng: &mut R,
    ) -> Result<(), Error<PC::Error>> {
        let verifier_init_state = IOPforPolyIdentity::init_verifier(
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

        let instance_degree_fn =
            |query: &InstanceQuery| instance_oracles[query.index].get_degree();

        let mut max_degree = 0;
        for vo in vos {
            let vo_degree = vo
                .get_expression()
                .degree(&wtns_degree_fn, &instance_degree_fn);

            max_degree = std::cmp::max(max_degree, vo_degree);
        }

        let quotient_degree = max_degree - vanishing_polynomial.degree();
        // println!("quotient degree {}", quotient_degree);

        let num_of_quotient_chunks = quotient_degree / srs_size
            + if quotient_degree % srs_size != 0 {
                1
            } else {
                0
            };

        if num_of_quotient_chunks != proof.commitments[1].len() {
            return Err(Error::TooManyChunks);
        }

        let mut quotient_chunks =
            Vec::<VerifierConcreteOracle<F, PC>>::with_capacity(
                num_of_quotient_chunks,
            );
        for i in 0..num_of_quotient_chunks {
            quotient_chunks.push(VerifierConcreteOracle {
                label: format!("quotient_chunk_{}", i).to_string(),
                should_mask: false,
                queried_rotations: BTreeSet::from([Rotation::curr()]),
                eval_at_rotation: BTreeMap::new(),
                evals_at_challenges: BTreeMap::new(),
                commitment: None,
            })
        }

        // --------------------------------------------------------------------
        // First round

        let first_comms = &proof.commitments[0];
        fs_rng.absorb(&to_bytes![first_comms].unwrap());

        let (verifier_first_msg, verifier_state) =
            IOPforPolyIdentity::verifier_first_round(
                verifier_init_state,
                &mut fs_rng,
            );

        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Second round

        let second_comms = &proof.commitments[1];
        fs_rng.absorb(&to_bytes![second_comms].unwrap());

        let (verifier_second_msg, verifier_state) =
            IOPforPolyIdentity::verifier_second_round(
                verifier_state,
                &mut fs_rng,
            );

        // --------------------------------------------------------------------

        let commitment_labels = witness_oracles
            .iter()
            .chain(quotient_chunks.iter())
            .map(|oracle| oracle.label.clone());

        let commitments: Vec<_> = first_comms
            .iter()
            .chain(second_comms.iter())
            .zip(commitment_labels)
            .map(|(c, label)| LabeledCommitment::new(label, c.clone(), None))
            .collect();

        // BEGIN QUERY SET
        let domain = GeneralEvaluationDomain::<F>::new(domain_size).unwrap();
        let omegas = domain.elements().collect();
        let mut query_set = QuerySet::<F>::new();
        for vo in vos {
            let q_set_i = vo
                .get_linearisation_expression()
                .compute_linearisation_query_set(
                    &|query: &LinearisationOracleQuery| {
                        let oracle = match query.oracle_type {
                            concrete_oracle::OracleType::Witness => {
                                &witness_oracles[query.index]
                            }
                            concrete_oracle::OracleType::Instance => {
                                return vec![]
                            } // Do not commit&open on instance
                        };

                        let point_info = oracle.get_point_info(
                            verifier_second_msg.label,
                            verifier_second_msg.xi,
                            &omegas,
                            query.rotation,
                        );
                        vec![(oracle.label.clone(), point_info)]
                    },
                );

            query_set.extend(q_set_i);
        }

        // Append quotient chunks queries to query_set
        for chunk in &quotient_chunks {
            let point_info = chunk.get_point_info(
                verifier_second_msg.label,
                verifier_second_msg.xi,
                &omegas,
                Rotation::curr(),
            );
            query_set.insert((chunk.label.clone(), point_info));
        }
        // END QUERY SET

        println!("query set: {:?}", query_set);

        assert_eq!(query_set.len(), proof.evaluations.len());

        let wtns_oracle_label_index_mapping = witness_oracles
            .iter()
            .enumerate()
            .map(|(i, oracle)| (oracle.label.clone(), i))
            .collect::<BTreeMap<String, usize>>();

        let quotient_chunks_label_index_mapping = quotient_chunks
            .iter()
            .enumerate()
            .map(|(i, oracle)| (oracle.label.clone(), i))
            .collect::<BTreeMap<String, usize>>();

        let quotient_chunk_regex =
            regex::Regex::new(r"^quotient_chunk_\d+$").unwrap();
        // ((poly_label, point), &evaluation)
        let evaluations: BTreeMap<(String, F), F> = query_set
            .iter()
            .zip(proof.evaluations.iter())
            .map(|((poly_label, (_point_label, point)), &evaluation)| {
                if quotient_chunk_regex.is_match(&poly_label) {
                    match quotient_chunks_label_index_mapping.get(poly_label) {
                        Some(index) => quotient_chunks[*index]
                            .register_eval_at_challenge(*point, evaluation),
                        None => {
                            panic!("Missing quotient chunk: {}", poly_label)
                        }
                    };
                } else {
                    match wtns_oracle_label_index_mapping.get(poly_label) {
                        Some(index) => witness_oracles[*index]
                            .register_eval_at_challenge(*point, evaluation),
                        None => panic!("Missing poly: {}", poly_label),
                    };
                }

                // println!("point_label: {} point: {}", point_label, point);

                ((poly_label.clone(), point.clone()), evaluation)
            })
            .collect();

        // BEGIN LINEARISATION POLY
        let info = LinearisationInfo {
            domain_size,
            opening_challenge: verifier_second_msg.xi,
        };

        let mut linearisation_poly =
            LinearisationPolyCommitment::<F, PC>::zero();

        for vo in vos {
            let linearisation_i = vo.get_linearisation_expression().evaluate(
                &|x: F| LinearisationPolyCommitment::from_const(x),
                &|_: &WitnessQuery| {
                    // let oracle = &state.witness_oracles[query.get_index()];
                    // oracle.query(&query.rotation, &query_context)
                    panic!("Not allowed here")
                },
                &|_: &InstanceQuery| {
                    // let oracle = &state.instance_oracles[query.get_index()];
                    // oracle.query(&query.rotation, &query_context)
                    panic!("Not allowed here")
                },
                &|x: LinearisationPolyCommitment<F, PC>| -x,
                &|x: LinearisationPolyCommitment<F, PC>,
                  y: LinearisationPolyCommitment<F, PC>| x + y,
                &|x: LinearisationPolyCommitment<F, PC>,
                  y: LinearisationPolyCommitment<F, PC>| {
                    // TODO: do better order of ifs
                    if !x.is_const() && !y.is_const() {
                        panic!("Equation is not linearised correctly")
                    }

                    if x.is_const() {
                        y * x.r0
                    } else if y.is_const() {
                        x * y.r0
                    } else {
                        LinearisationPolyCommitment::from_const(x.r0 * y.r0)
                    }
                },
                &|x: LinearisationPolyCommitment<F, PC>, y: F| x * y,
                &|query: &LinearisationOracleQuery| {
                    let query_response: LinearisationQueryResponse<F, PC> =
                        match query.oracle_type {
                            OracleType::Witness => witness_oracles[query.index]
                                .query_for_linearisation(
                                    &query.rotation,
                                    &query.ctx,
                                    &info,
                                ),
                            OracleType::Instance => instance_oracles
                                [query.index]
                                .query_for_linearisation(
                                    &query.rotation,
                                    &query.ctx,
                                    &info,
                                ),
                        };

                    match query_response {
                        LinearisationQueryResponse::Opening(x) => {
                            LinearisationPolyCommitment::from_const(x)
                        }
                        LinearisationQueryResponse::Poly(_) => {
                            panic!("Poly not possible from committed oracle")
                        }
                        LinearisationQueryResponse::Commitment(c) => {
                            LinearisationPolyCommitment::from_commitment(c)
                        }
                    }
                },
            );

            linearisation_poly = linearisation_poly + linearisation_i;
        }
        // END LINEARISATION POLY

        // --------------------------------------------------------------------
        // Third round

        // Linearisation commitment and eval are being derived by verifier
        //
        fs_rng.absorb(&to_bytes![linearisation_poly.comm].unwrap());

        // --------------------------------------------------------------------

        fs_rng.absorb(&proof.evaluations);

        let opening_challenge: F = u128::rand(&mut fs_rng).into();

        let res = PC::batch_check(
            &vk.verifier_key,
            &commitments,
            &query_set,
            &evaluations,
            &proof.opening_proof,
            opening_challenge,
            zk_rng,
        )
        .map_err(Error::from_pc_err)?;
        assert_eq!(res, true);

        let query_context = QueryContext::Opening(
            domain_size,
            QueryPoint::Challenge(verifier_second_msg.xi),
        );

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
                    oracle.query(&query.rotation, &query_context)
                },
                &|query: &InstanceQuery| {
                    let oracle = &instance_oracles[query.get_index()];
                    oracle.query(&query.rotation, &query_context)
                },
                &|x: F| -x,
                &|x: F, y: F| x + y,
                &|x: F, y: F| x * y,
                &|x: F, y: F| x * y,
                &|_: &LinearisationOracleQuery| {
                    panic!("Not allowed in this ctx")
                },
            );

            quotient_eval += powers_of_alpha[vo_index] * vo_evaluation;
        }

        let x_n = verifier_second_msg.xi.pow([srs_size as u64, 0, 0, 0]);
        let powers_of_x: Vec<F> =
            successors(Some(F::one()), |x_i| Some(*x_i * x_n))
                .take(quotient_chunks.len())
                .collect();

        let mut t_part = F::zero();
        for (&x_i, t_i) in powers_of_x.iter().zip(quotient_chunks.iter()) {
            t_part += x_i * t_i.query(&Rotation::curr(), &query_context);
        }

        t_part *= vanishing_polynomial.evaluate(&verifier_second_msg.xi);

        quotient_eval -= t_part;

        if quotient_eval != F::zero() {
            return Err(Error::QuotientNotZero);
        }

        Ok(())
    }
}
