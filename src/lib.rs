use std::collections::{BTreeMap, BTreeSet};
use std::iter::{self, successors};
use std::marker::PhantomData;

use ark_ff::{to_bytes, PrimeField};
use ark_poly::univariate::DensePolynomial;
use ark_poly::{
    EvaluationDomain, GeneralEvaluationDomain, Polynomial, UVPolynomial,
};
use ark_poly_commit::{LabeledPolynomial, PCUniversalParams};

use ark_std::rand::{Rng, RngCore};
use commitment::HomomorphicCommitment;
use data_structures::{
    Proof, ProverKey, ProverPreprocessedInput, UniversalSRS, VerifierKey,
    VerifierPreprocessedInput,
};
use error::Error;
use multiproof::piop::Multiopen;
use oracles::instance::{InstanceProverOracle, InstanceVerifierOracle};
use piop::error::Error as PiopError;

use oracles::traits::{ConcreteOracle, Instantiable};
use oracles::witness::{WitnessProverOracle, WitnessVerifierOracle};
use piop::PIOPforPolyIdentity;
use rng::FiatShamirRng;
use vo::VirtualOracle;

use crate::lookup::LookupArgument;

use crate::oracles::query::OracleType;
use crate::oracles::rotation::{Rotation, Sign};
use crate::oracles::traits::CommittedOracle;

use crate::util::evaluate_query_set;

pub mod commitment;
pub mod data_structures;
pub mod error;
pub mod oracles;
pub mod piop;
pub mod rng;
mod util;
pub mod vo;

pub mod indexer;
pub mod lookup;
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
        preprocessed: &ProverPreprocessedInput<F, PC>,
        witness_oracles: &'a mut [WitnessProverOracle<F>],
        instance_oracles: &'a mut [InstanceProverOracle<F>],
        vos: &[&'a dyn VirtualOracle<F>], // TODO: this should be in index
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

        let mut prover_state = PIOPforPolyIdentity::init_prover(
            witness_oracles,
            instance_oracles,
            vos,
            domain_size,
            vanishing_polynomial,
            preprocessed,
        );

        let verifier_init_state = PIOPforPolyIdentity::<F, PC>::init_verifier(
            domain_size,
            vanishing_polynomial,
        );

        let (verifier_lookup_aggregation_msg, verifier_state) =
            PIOPforPolyIdentity::<F, PC>::verifier_lookup_aggregation_round(
                verifier_init_state,
                &mut fs_rng,
            );

        // --------------------------------------------------------------------
        // Lookup round

        /*
            Each lookup is consisted of: a, a', s, s' and z
            a and s evaluations are derived on verifier side because of homomorphic property
            So for each lookup provide:
                commitments: a', s', z
                evaluations: a' at x, a' at w^-1x, s' at x, z at x, z at wx, each table_oracle evaluation at x


            First compute a, s, a' and s', commit and derive theta. Then start permutation round to derive beta and gamma and then derive
            subset equality checks with beta and gamma
        */

        let lookup_polys = PIOPforPolyIdentity::prover_lookup_round(
            &verifier_lookup_aggregation_msg,
            &mut prover_state,
            preprocessed,
            &pk.vk.index_info,
            zk_rng,
        )?;

        let lookup_polys_to_open = lookup_polys
            .iter()
            .map(|(_, _, a_prime, s_prime)| vec![a_prime, s_prime])
            .flatten();

        let lookup_prime_labeled: Vec<
            LabeledPolynomial<F, DensePolynomial<F>>,
        > = lookup_polys
            .iter()
            .map(|(_, _, a_prime, s_prime)| {
                vec![a_prime.to_labeled(), s_prime.to_labeled()]
            })
            .flatten()
            .collect();

        // commit to a_prime and s_prime for each lookup
        let (lookup_commitments, lookup_rands) =
            PC::commit(&pk.committer_key, &lookup_prime_labeled, Some(zk_rng))
                .map_err(Error::from_pc_err)?;

        fs_rng.absorb(&to_bytes![lookup_commitments].unwrap());

        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Permutation round

        let (verifier_permutation_msg, verifier_state) =
            PIOPforPolyIdentity::<F, PC>::verifier_permutation_round(
                verifier_state,
                &mut fs_rng,
            );

        // TODO: rename z_polys to permutation_aggregation_polys
        let z_polys: Vec<WitnessProverOracle<F>> =
            PIOPforPolyIdentity::prover_permutation_round(
                &verifier_permutation_msg,
                &mut prover_state,
                &pk.vk.index_info.permutation_argument,
                preprocessed,
                &pk.vk.index_info.extended_coset_domain,
                zk_rng,
            );

        let z_polys_labeled: Vec<_> =
            z_polys.iter().map(|z| z.to_labeled()).collect();
        // commit to z oracles
        let (z_commitments, z_rands) =
            PC::commit(&pk.committer_key, &z_polys_labeled, Some(zk_rng))
                .map_err(Error::from_pc_err)?;

        fs_rng.absorb(&to_bytes![z_commitments].unwrap());

        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Lookup subset equality round

        let lookup_z_polys =
            PIOPforPolyIdentity::<F, PC>::prover_lookup_subset_equality_round(
                &verifier_permutation_msg,
                &lookup_polys,
                &mut prover_state,
                &pk.vk.index_info,
                zk_rng,
            );

        // get labeled polys of witness oracles
        let lookup_z_polys_labeled: Vec<
            LabeledPolynomial<F, DensePolynomial<F>>,
        > = lookup_z_polys
            .iter()
            .map(|oracle| oracle.to_labeled())
            .collect();

        // commit to witness oracles
        let (lookup_z_commitments, lookup_z_rands) = PC::commit(
            &pk.committer_key,
            &lookup_z_polys_labeled,
            Some(zk_rng),
        )
        .map_err(Error::from_pc_err)?;

        fs_rng.absorb(&to_bytes![lookup_z_commitments].unwrap());

        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Quotient round

        let (verifier_first_msg, verifier_state) =
            PIOPforPolyIdentity::<F, PC>::verifier_first_round(
                verifier_state,
                &mut fs_rng,
            );

        let quotient_chunk_oracles =
            PIOPforPolyIdentity::prover_quotient_round(
                &verifier_permutation_msg,
                &verifier_first_msg,
                &mut prover_state,
                &pk.vk,
                &preprocessed,
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

        // TODO!!!! PUT ALL EVALS IN TRANSCRIPT

        // Compute witness evals
        let witness_query_set = PIOPforPolyIdentity::<F, PC>::get_query_set(
            &witness_oracles,
            verifier_second_msg.label,
            verifier_second_msg.xi,
            &omegas,
        );

        let witness_evals: Vec<F> =
            evaluate_query_set(witness_oracles, &witness_query_set)?;

        // fs_rng.absorb(&to_bytes![witness_evals].unwrap());
        // Compute fixed evals

        let fixed_query_set = PIOPforPolyIdentity::<F, PC>::get_query_set(
            &preprocessed.fixed_oracles,
            verifier_second_msg.label,
            verifier_second_msg.xi,
            &omegas,
        );

        let fixed_oracle_evals: Vec<F> =
            evaluate_query_set(&preprocessed.fixed_oracles, &fixed_query_set)?;

        // Compute table evals
        let table_query_set = PIOPforPolyIdentity::<F, PC>::get_query_set(
            &preprocessed.table_oracles,
            verifier_second_msg.label,
            verifier_second_msg.xi,
            &omegas,
        );

        let table_oracle_evals: Vec<F> =
            evaluate_query_set(&preprocessed.table_oracles, &table_query_set)?;

        // Compute lookup evals
        // For each lookup argument we will always put it in same order:
        // a' at x, a' at w^-1x, s' at x and z at x, a at wx
        let omega = domain.element(1);
        let omega_inv = omega.inverse().unwrap();
        let mut lookup_evals = Vec::with_capacity(3 * lookup_polys.len());
        for (_, _, a_prime, s_prime) in lookup_polys.iter() {
            let a_prime_at_x = a_prime.query(&verifier_second_msg.xi)?;
            let a_prime_at_minus_w_x =
                a_prime.query(&(verifier_second_msg.xi * omega_inv))?;

            let s_prime_at_x = s_prime.query(&verifier_second_msg.xi)?;
            lookup_evals.extend(vec![
                a_prime_at_x,
                a_prime_at_minus_w_x,
                s_prime_at_x,
            ]);
        }

        let mut lookup_z_evals = Vec::with_capacity(2 * lookup_z_polys.len());
        for z in lookup_z_polys.iter() {
            let z_at_x = z.query(&verifier_second_msg.xi)?;
            let z_at_omega_x = z.query(&(verifier_second_msg.xi * omega))?;
            lookup_z_evals.extend(vec![z_at_x, z_at_omega_x]);
        }

        // Compute quotient chunk evals
        // There are no rotations for q_i-s so we can just query at evaluation point
        let quotient_chunks_evals: Vec<F> = quotient_chunk_oracles
            .iter()
            .map(|q_i| q_i.query(&verifier_second_msg.xi))
            .collect::<Result<Vec<F>, PiopError>>()?;

        // Compute permutation oracle evals
        // There are no rotations for sigma_i-s so we can just query at evaluation point
        let permutation_oracle_evals: Vec<F> = preprocessed
            .permutation_oracles
            .iter()
            .map(|sigma_i| sigma_i.query(&verifier_second_msg.xi))
            .collect::<Result<Vec<F>, PiopError>>()?;

        // Compute z polys oracle evals
        let z_query_set = PIOPforPolyIdentity::<F, PC>::get_query_set(
            &z_polys,
            verifier_second_msg.label,
            verifier_second_msg.xi,
            &omegas,
        );

        let z_evals = evaluate_query_set(&z_polys, &z_query_set)?;

        // compute q_blind eval
        let q_blind_eval = preprocessed
            .q_blind
            .polynomial()
            .evaluate(&verifier_second_msg.xi);

        // Multiopen
        let mut oracles: Vec<&dyn Instantiable<F>> = witness_oracles
            .iter()
            .chain(lookup_polys_to_open)
            .chain(lookup_z_polys.iter())
            .chain(quotient_chunk_oracles.iter())
            .chain(z_polys.iter())
            .map(|o| o as &dyn Instantiable<F>)
            .collect();
        let preprocessed_oracles: Vec<&dyn Instantiable<F>> = preprocessed
            .fixed_oracles
            .iter()
            .chain(preprocessed.table_oracles.iter())
            .chain(preprocessed.permutation_oracles.iter())
            .chain(iter::once(&preprocessed.q_blind))
            .map(|o| o as &dyn Instantiable<F>)
            .collect();

        oracles.extend_from_slice(&preprocessed_oracles.as_slice());

        let oracle_rands: Vec<PC::Randomness> = wtns_rands
            .iter()
            .chain(lookup_rands.iter())
            .chain(lookup_z_rands.iter())
            .chain(quotient_rands.iter())
            .chain(z_rands.iter())
            .chain(preprocessed.empty_rands_for_fixed.iter())
            .map(|rand| rand.clone())
            .collect();

        assert_eq!(oracles.len(), oracle_rands.len());

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
            // witness oracles
            witness_commitments: witness_commitments
                .iter()
                .map(|c| c.commitment().clone())
                .collect(),
            witness_evals,

            // fixed
            fixed_oracle_evals,
            table_oracle_evals,
            permutation_oracle_evals,
            q_blind_eval,

            // lookups part
            lookup_commitments: lookup_commitments
                .iter()
                .map(|c| c.commitment().clone())
                .collect(),
            lookup_evals,
            lookup_z_commitments: lookup_z_commitments
                .iter()
                .map(|c| c.commitment().clone())
                .collect(),
            lookup_z_evals,

            // permutation aggregation
            z_commitments: z_commitments
                .iter()
                .map(|c| c.commitment().clone())
                .collect(),
            z_evals,
            // quotient part
            quotient_chunk_commitments: quotient_chunk_commitments
                .iter()
                .map(|c| c.commitment().clone())
                .collect(),
            quotient_chunks_evals,
            // multiopen
            multiopen_proof,
        };

        // TODO: include permutation checks
        /* BEGIN SANITY CHECK BEFORE INVOKING VERIFIER */
        // let powers_of_alpha: Vec<F> = successors(Some(F::one()), |alpha_i| {
        //     Some(*alpha_i * verifier_first_msg.alpha)
        // })
        // .take(vos.len())
        // .collect();

        // let mut quotient_eval = F::zero();
        // let evaluate_vo = |vo: &&dyn VirtualOracle<F>, c: F| {
        //     let vo_evaluation = vo.get_expression().evaluate(
        //         &|x: F| x,
        //         &|query| {
        //             let challenge = query.rotation.compute_evaluation_point(
        //                 c,
        //                 &omegas,
        //             );
        //             match query.oracle_type {
        //                 OracleType::Witness => {
        //                     match prover_state.witness_oracles_mapping.get(&query.label) {
        //                         Some(index) => prover_state.witness_oracles[*index].query(&challenge),
        //                         None => panic!("Witness oracle with label add_label not found") //TODO: Introduce new Error here,
        //                     }
        //                 },
        //                 OracleType::Instance => {
        //                     match prover_state.instance_oracles_mapping.get(&query.label) {
        //                         Some(index) => prover_state.instance_oracles[*index].query(&challenge),
        //                         None => panic!("Instance oracle with label {} not found", query.label) //TODO: Introduce new Error here,
        //                     }
        //                 },
        //                 OracleType::Fixed => {
        //                     match prover_state.fixed_oracles_mapping.get(&query.label) {
        //                         Some(index) => preprocessed.fixed_oracles[*index].query(&challenge),
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
        //     vo_evaluation
        // };
        // // Check all VOs expressions are 0 in ALL the domain. If some other vanishing poly is being
        // // used this check may fail and the proof could still be valid!
        // for (row_n, omega) in omegas.iter().enumerate() {
        //     for (vo_index, vo) in vos.iter().enumerate() {
        //         let vo_evaluation = evaluate_vo(vo, *omega);

        //         if vo_evaluation != F::zero() {
        //             panic!("VO number {} failed at row {}", vo_index, row_n);
        //         }
        //     }
        // }

        // for (vo_index, vo) in vos.iter().enumerate() {
        //     let vo_evaluation = evaluate_vo(vo, verifier_second_msg.xi);

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
        //     t_part += x_i * t_i.query(&verifier_second_msg.xi);
        // }

        // t_part *= vanishing_polynomial.evaluate(&verifier_second_msg.xi);

        // quotient_eval -= t_part;
        // assert_eq!(quotient_eval, F::zero());
        /* END SANITY CHECK BEFORE INVOKING VERIFIER */

        Ok(proof)
    }

    pub fn verify<R: Rng>(
        vk: &VerifierKey<F, PC>,
        preprocessed: &mut VerifierPreprocessedInput<F, PC>,
        proof: Proof<F, PC>,
        witness_oracles: &mut [WitnessVerifierOracle<F, PC>],
        instance_oracles: &mut [InstanceVerifierOracle<F>],
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
        let fixed_oracles_mapping: BTreeMap<String, usize> = preprocessed
            .fixed_oracles
            .iter()
            .enumerate()
            .map(|(i, oracle)| (oracle.get_label(), i))
            .collect();
        let table_oracles_mapping: BTreeMap<String, usize> = preprocessed
            .table_oracles
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

        let (verifier_lookup_aggregation_msg, verifier_state) =
            PIOPforPolyIdentity::<F, PC>::verifier_lookup_aggregation_round(
                verifier_init_state,
                &mut fs_rng,
            );

        fs_rng.absorb(&to_bytes![&proof.lookup_commitments].unwrap());

        let (verifier_permutation_msg, verifier_state) =
            PIOPforPolyIdentity::<F, PC>::verifier_permutation_round(
                verifier_state,
                &mut fs_rng,
            );

        fs_rng.absorb(&to_bytes![&proof.z_commitments].unwrap());

        fs_rng.absorb(&to_bytes![&proof.lookup_z_commitments].unwrap());

        let (verifier_first_msg, verifier_state) =
            PIOPforPolyIdentity::<F, PC>::verifier_first_round(
                verifier_state,
                &mut fs_rng,
            );

        fs_rng.absorb(&to_bytes![&proof.quotient_chunk_commitments].unwrap());

        let (verifier_second_msg, _verifier_state) =
            PIOPforPolyIdentity::<F, PC>::verifier_second_round(
                verifier_state,
                &mut fs_rng,
            );

        // Map evals to each oracle
        for (witness_oracle, commitment) in witness_oracles
            .iter_mut()
            .zip(proof.witness_commitments.iter())
        {
            witness_oracle.register_commitment(commitment.clone());
        }

        // Quotient chunks are evaluated only in evaluation challenge
        let quotient_chunk_oracles = (0..num_of_quotient_chunks)
            .map(|i| WitnessVerifierOracle {
                label: format!("quotient_chunk_{}", i).to_string(),
                queried_rotations: BTreeSet::from([Rotation::curr()]),
                should_permute: false,
                evals_at_challenges: BTreeMap::from([(
                    verifier_second_msg.xi,
                    proof.quotient_chunks_evals[i],
                )]),
                commitment: Some(proof.quotient_chunk_commitments[i].clone()),
            })
            .collect::<Vec<_>>();

        let domain = GeneralEvaluationDomain::new(domain_size).unwrap();
        let omegas: Vec<F> = domain.elements().collect();

        // Map witness oracles evaluations
        let query_set = PIOPforPolyIdentity::<F, PC>::get_query_set(
            witness_oracles,
            verifier_second_msg.label,
            verifier_second_msg.xi,
            &omegas,
        );

        assert_eq!(query_set.len(), proof.witness_evals.len());

        // map claimed evaluations with proper oracles
        for ((poly_label, (_, point)), &evaluation) in
            query_set.iter().zip(proof.witness_evals.iter())
        {
            match witness_oracles_mapping.get(poly_label) {
                Some(index) => witness_oracles[*index]
                    .register_eval_at_challenge(*point, evaluation),
                None => {
                    return Err(PiopError::MissingWtnsOracle(
                        poly_label.clone(),
                    )
                    .into())
                }
            };
        }

        // Map fixed oracles evaluations
        let fixed_query_set = PIOPforPolyIdentity::<F, PC>::get_query_set(
            &preprocessed.fixed_oracles,
            verifier_second_msg.label,
            verifier_second_msg.xi,
            &omegas,
        );

        assert_eq!(fixed_query_set.len(), proof.fixed_oracle_evals.len());

        for ((poly_label, (_, point)), &evaluation) in
            fixed_query_set.iter().zip(proof.fixed_oracle_evals.iter())
        {
            match fixed_oracles_mapping.get(poly_label) {
                Some(index) => preprocessed.fixed_oracles[*index]
                    .register_eval_at_challenge(*point, evaluation),
                None => {
                    return Err(PiopError::MissingFixedOracle(
                        poly_label.clone(),
                    )
                    .into())
                }
            };
        }

        // Map table oracles evaluations
        let table_query_set = PIOPforPolyIdentity::<F, PC>::get_query_set(
            &preprocessed.table_oracles,
            verifier_second_msg.label,
            verifier_second_msg.xi,
            &omegas,
        );

        assert_eq!(table_query_set.len(), proof.table_oracle_evals.len());

        for ((poly_label, (_, point)), &evaluation) in
            table_query_set.iter().zip(proof.table_oracle_evals.iter())
        {
            match table_oracles_mapping.get(poly_label) {
                Some(index) => preprocessed.table_oracles[*index]
                    .register_eval_at_challenge(*point, evaluation),
                None => {
                    return Err(PiopError::MissingLUTableOracle(
                        poly_label.clone(),
                    )
                    .into())
                }
            };
        }

        // Map permutation evals
        // Permutation oracles are opened just in evaluation challenge
        assert_eq!(
            preprocessed.permutation_oracles.len(),
            proof.permutation_oracle_evals.len()
        );
        for (sigma, &eval) in preprocessed
            .permutation_oracles
            .iter_mut()
            .zip(proof.permutation_oracle_evals.iter())
        {
            sigma.register_eval_at_challenge(verifier_second_msg.xi, eval);
        }

        let oracles_to_copy: Vec<&WitnessVerifierOracle<F, PC>> =
            witness_oracles
                .iter()
                .filter(|&oracle| oracle.should_permute)
                .collect();

        // Lookups parts
        /*
            Each lookup is consisted of: a, a', s, s' and z
            a and s evaluations are derived on verifier side because of homomorphic property
            So for each lookup provide:
                commitments: a', s', z
                evaluations: a' at x, a' at w^-1x, s' at x, z at x, z at wx, each table_oracle evaluation at x
        */
        let omega = domain.element(1);
        let omega_inv = omega.inverse().unwrap();
        let evaluation_challenge = verifier_second_msg.xi;

        let lookup_permuted_oracles_commitments =
            proof.lookup_commitments.chunks(2);
        assert_eq!(
            lookup_permuted_oracles_commitments.len(),
            vk.index_info.lookups.len()
        );

        let lookup_permuted_oracles_evals = proof.lookup_evals.chunks(3);
        assert_eq!(
            lookup_permuted_oracles_evals.len(),
            vk.index_info.lookups.len()
        );

        let lookup_polys: Vec<_> = vk
            .index_info
            .lookups
            .iter()
            .zip(lookup_permuted_oracles_commitments)
            .zip(lookup_permuted_oracles_evals)
            .enumerate()
            .map(
                |(
                    lookup_index,
                    ((lookup_vo, permuted_commitments), permuted_evals),
                )|
                 -> Result<_, Error<PC::Error>> {
                    let (a, s) =
                LookupArgument::construct_a_and_s_unpermuted_polys_verifier(
                    &witness_oracles_mapping,
                    &instance_oracles_mapping,
                    &fixed_oracles_mapping,
                    &table_oracles_mapping,
                    witness_oracles,
                    instance_oracles,
                    &preprocessed.fixed_oracles,
                    &preprocessed.table_oracles,
                    lookup_index,
                    lookup_vo.get_expressions(),
                    lookup_vo.get_table_queries(),
                    verifier_lookup_aggregation_msg.theta,
                    verifier_second_msg.xi,
                    &omegas,
                )?;

                    let a_prime = WitnessVerifierOracle::<F, PC> {
                        label: format!("lookup_a_prime_{}_poly", lookup_index)
                            .to_string(),
                        queried_rotations: BTreeSet::from([
                            Rotation::curr(),
                            Rotation::prev(),
                        ]),
                        evals_at_challenges: BTreeMap::from([
                            (evaluation_challenge, permuted_evals[0]),
                            (
                                evaluation_challenge * omega_inv,
                                permuted_evals[1],
                            ),
                        ]),
                        commitment: Some(permuted_commitments[0].clone()),
                        should_permute: false,
                    };

                    let s_prime = WitnessVerifierOracle::<F, PC> {
                        label: format!("lookup_s_prime_{}_poly", lookup_index)
                            .to_string(),
                        queried_rotations: BTreeSet::from([Rotation::curr()]),
                        evals_at_challenges: BTreeMap::from([(
                            evaluation_challenge,
                            permuted_evals[2],
                        )]),
                        commitment: Some(permuted_commitments[1].clone()),
                        should_permute: false,
                    };

                    Ok((a, s, a_prime, s_prime))
                },
            )
            .collect::<Result<_, _>>()?;

        let lookup_polys_to_check_in_opening = lookup_polys
            .iter()
            .map(|(_, _, a_prime, s_prime)| vec![a_prime, s_prime])
            .flatten();

        let lookup_z_evals_chunks = proof.lookup_z_evals.chunks(2);
        assert_eq!(
            proof.lookup_z_commitments.len(),
            vk.index_info.lookups.len()
        );
        assert_eq!(lookup_z_evals_chunks.len(), vk.index_info.lookups.len());

        let lookup_z_polys = proof
            .lookup_z_commitments
            .iter()
            .zip(lookup_z_evals_chunks)
            .enumerate()
            .map(|(lookup_index, (z_commitment, evals))| {
                WitnessVerifierOracle::<F, PC> {
                    label: format!("lookup_{}_agg_poly", lookup_index)
                        .to_string(),
                    queried_rotations: BTreeSet::from([
                        Rotation::curr(),
                        Rotation::next(),
                    ]),
                    evals_at_challenges: BTreeMap::from([
                        (evaluation_challenge, evals[0]),
                        (evaluation_challenge * omega, evals[1]),
                    ]),
                    commitment: Some(z_commitment.clone()),
                    should_permute: false,
                }
            })
            .collect::<Vec<WitnessVerifierOracle<F, PC>>>();
        // end lookups

        // Map z permutation oracles
        let num_of_z_polys = vk
            .index_info
            .permutation_argument
            .number_of_z_polys(oracles_to_copy.len());
        assert_eq!(num_of_z_polys, proof.z_commitments.len());

        // Each z is evaluated at: x, wx and w^ux(except the last one)
        let mut z_polys: Vec<_> = proof
            .z_commitments
            .iter()
            .enumerate()
            .map(|(i, zi)| {
                let mut queried_rotations =
                    BTreeSet::from([Rotation::curr(), Rotation::next()]);

                // if not last append w^ux
                if i != num_of_z_polys - 1 {
                    queried_rotations.insert(Rotation::new(
                        vk.index_info.permutation_argument.usable_rows,
                        Sign::Plus,
                    ));
                }

                WitnessVerifierOracle::<F, PC> {
                    label: format!("agg_permutation_{}", i).to_string(),
                    queried_rotations,
                    evals_at_challenges: BTreeMap::default(),
                    commitment: Some(zi.clone()),
                    should_permute: false,
                }
            })
            .collect();

        let z_query_set = PIOPforPolyIdentity::<F, PC>::get_query_set(
            &z_polys,
            verifier_second_msg.label,
            verifier_second_msg.xi,
            &omegas,
        );

        assert_eq!(z_query_set.len(), proof.z_evals.len());

        let z_mapping: BTreeMap<String, usize> = z_polys
            .iter()
            .enumerate()
            .map(|(i, oracle)| (oracle.get_label(), i))
            .collect();

        for ((poly_label, (_point_label, point)), &evaluation) in
            z_query_set.iter().zip(proof.z_evals.iter())
        {
            match z_mapping.get(poly_label) {
                Some(index) => z_polys[*index]
                    .register_eval_at_challenge(*point, evaluation),
                None => {
                    return Err(PiopError::MissingPermutationOracle(
                        poly_label.clone(),
                    )
                    .into())
                }
            };
        }

        preprocessed.q_blind.register_eval_at_challenge(
            verifier_second_msg.xi,
            proof.q_blind_eval.clone(),
        );

        // END CHALLENGE => EVALS MAPPING

        let powers_of_alpha: Vec<F> = successors(Some(F::one()), |alpha_i| {
            Some(*alpha_i * verifier_first_msg.alpha)
        })
        .take(vos.len())
        .collect();

        let number_of_alphas = vk
            .index_info
            .permutation_argument
            .number_of_alphas(z_polys.len());

        // start from next of last power of alpha
        let permutation_begin_with =
            powers_of_alpha.last().unwrap().clone() * verifier_first_msg.alpha;
        let permutation_alphas: Vec<F> =
            successors(Some(permutation_begin_with), |alpha_i| {
                Some(*alpha_i * verifier_first_msg.alpha)
            })
            .take(number_of_alphas)
            .collect();

        // For each lookup argument we need 5 alphas
        // Again begin with last alpha after permutation argument
        let lookups_begin_with = if let Some(alpha) = permutation_alphas.last()
        {
            alpha.clone()
        } else {
            powers_of_alpha.last().unwrap().clone()
        };

        let lookup_alphas: Vec<F> =
            successors(Some(lookups_begin_with), |alpha_i| {
                Some(*alpha_i * verifier_first_msg.alpha)
            })
            .take(5 * vk.index_info.lookups.len())
            .collect();

        let lookup_alpha_chunks: Vec<&[F]> = lookup_alphas.chunks(5).collect();

        // TODO: ENABLE FAST LAGRANGE EVALUATION
        let mut l0_evals = vec![F::zero(); domain_size];
        l0_evals[0] = F::one();
        let l0 =
            DensePolynomial::from_coefficients_slice(&domain.ifft(&l0_evals));

        let mut lu_evals = vec![F::zero(); domain_size];
        lu_evals[vk.index_info.permutation_argument.usable_rows] = F::one();
        let lu =
            DensePolynomial::from_coefficients_slice(&domain.ifft(&lu_evals));

        let l0_eval = l0.evaluate(&verifier_second_msg.xi);
        let lu_eval = lu.evaluate(&verifier_second_msg.xi);

        let mut quotient_eval = F::zero();
        for (vo_index, vo) in vos.iter().enumerate() {
            let vo_evaluation = vo.get_expression().evaluate(
                &|x| Ok(x),
                &|query| {
                    let challenge = query.rotation.compute_evaluation_point(
                        verifier_second_msg.xi,
                        &omegas,
                    );
                    //TODO Add Error handling
                    match query.oracle_type {
                        OracleType::Witness => {
                            match witness_oracles_mapping.get(&query.label) {
                                Some(index) => {
                                    witness_oracles[*index].query(&challenge)
                                }
                                None => Err(PiopError::MissingWtnsOracle(
                                    query.label.clone(),
                                )),
                            }
                        }
                        OracleType::Instance => {
                            match instance_oracles_mapping.get(&query.label) {
                                Some(index) => {
                                    instance_oracles[*index].query(&challenge)
                                }
                                None => Err(PiopError::MissingInstanceOracle(
                                    query.label.clone(),
                                )),
                            }
                        }
                        OracleType::Fixed => {
                            match fixed_oracles_mapping.get(&query.label) {
                                Some(index) => preprocessed.fixed_oracles
                                    [*index]
                                    .query(&challenge),
                                None => Err(PiopError::MissingFixedOracle(
                                    query.label.clone(),
                                )),
                            }
                        }
                    }
                },
                &|x| x.and_then(|x_val| Ok(-x_val)),
                &|x, y| {
                    x.and_then(|x_val| y.and_then(|y_val| Ok(x_val + y_val)))
                },
                &|x, y| {
                    x.and_then(|x_val| y.and_then(|y_val| Ok(x_val * y_val)))
                },
                &|x, y| x.and_then(|x_val| Ok(x_val * y)),
            )?;

            quotient_eval += powers_of_alpha[vo_index] * vo_evaluation;
        }

        // Permutation argument
        // If there are no oracles to enforce copy constraints on, we just return zero
        quotient_eval += if oracles_to_copy.len() > 0 {
            vk.index_info.permutation_argument.open_argument(
                l0_eval,
                lu_eval,
                &preprocessed.q_blind,
                &z_polys,
                &preprocessed.permutation_oracles,
                oracles_to_copy.as_slice(),
                verifier_permutation_msg.beta,
                verifier_permutation_msg.gamma,
                &domain,
                verifier_second_msg.xi,
                &permutation_alphas,
            )?
        } else {
            F::zero()
        };

        // Lookup contribution to quotient
        for ((lookup_oracles, z), &alpha_powers) in lookup_polys
            .iter()
            .zip(lookup_z_polys.iter())
            .zip(lookup_alpha_chunks.iter())
        {
            let (a, s, a_prime, s_prime) = lookup_oracles;
            quotient_eval += LookupArgument::open_argument(
                &l0_eval,
                lu_eval,
                &preprocessed.q_blind,
                a,
                s,
                a_prime,
                s_prime,
                z,
                verifier_permutation_msg.beta,
                verifier_permutation_msg.gamma,
                &verifier_second_msg.xi,
                &domain,
                alpha_powers,
            )?
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
            t_part += x_i * t_i.query(&verifier_second_msg.xi)?;
        }

        t_part *= vanishing_polynomial.evaluate(&verifier_second_msg.xi);

        quotient_eval -= t_part;

        if quotient_eval != F::zero() {
            return Err(Error::QuotientNotZero);
        }

        let mut oracles: Vec<&dyn CommittedOracle<F, PC>> = witness_oracles
            .iter()
            .chain(lookup_polys_to_check_in_opening)
            .chain(lookup_z_polys.iter())
            .chain(quotient_chunk_oracles.iter())
            .chain(z_polys.iter())
            .map(|a| a as &dyn CommittedOracle<F, PC>)
            .collect();
        let preprocessed_oracles: Vec<&dyn CommittedOracle<F, PC>> =
            preprocessed
                .fixed_oracles
                .iter()
                .chain(preprocessed.table_oracles.iter())
                .chain(preprocessed.permutation_oracles.iter())
                .chain(iter::once(&preprocessed.q_blind))
                .map(|o| o as &dyn CommittedOracle<F, PC>)
                .collect();

        oracles.extend_from_slice(&preprocessed_oracles.as_slice());

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
