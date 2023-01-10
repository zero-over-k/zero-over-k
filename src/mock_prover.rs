use std::collections::{BTreeMap, BTreeSet};
use std::iter::{self, successors};
use std::marker::PhantomData;

use ark_ff::{to_bytes, PrimeField};
use ark_poly::univariate::DensePolynomial;
use ark_poly::{
    EvaluationDomain, GeneralEvaluationDomain, Polynomial, UVPolynomial,
};
use ark_poly_commit::{LabeledPolynomial, PCUniversalParams};

use crate::commitment::HomomorphicCommitment;
use crate::data_structures::{
    Proof, ProverKey, ProverPreprocessedInput, UniversalSRS, VerifierKey,
    VerifierPreprocessedInput,
};
use crate::error::Error;
use crate::multiproof::piop::Multiopen;
use crate::oracles::instance::{InstanceProverOracle, InstanceVerifierOracle};
use crate::piop::error::Error as PiopError;
use ark_std::rand::{Rng, RngCore};

use crate::oracles::traits::{ConcreteOracle, Instantiable};
use crate::oracles::witness::{WitnessProverOracle, WitnessVerifierOracle};
use crate::piop::PIOPforPolyIdentity;
use crate::rng::FiatShamirRng;
use crate::vo::VirtualOracle;

use crate::lookup::LookupArgument;

use crate::oracles::query::OracleType;
use crate::oracles::rotation::{Rotation, Sign};
use crate::oracles::traits::CommittedOracle;

use crate::util::evaluate_query_set;
use crate::{PCKeys, PIL};

pub struct MockProver<
    F: PrimeField,
    PC: HomomorphicCommitment<F>,
    FS: FiatShamirRng,
> {
    _field: PhantomData<F>,
    _pc: PhantomData<PC>,
    _fs: PhantomData<FS>,
}

impl<F, PC, FS> PIL<F, PC, FS> for MockProver<F, PC, FS>
where
    F: PrimeField,
    PC: HomomorphicCommitment<F>,
    FS: FiatShamirRng,
{
    const PROTOCOL_NAME: &'static [u8] = b"MockProver";

    fn universal_setup<R: RngCore>(
        max_degree: usize,
        rng: &mut R,
    ) -> Result<UniversalSRS<F, PC>, Error<PC::Error>> {
        PC::setup(max_degree, None, rng).map_err(Error::from_pc_err)
    }

    fn prepare_keys(
        srs: &UniversalSRS<F, PC>,
    ) -> Result<PCKeys<F, PC>, Error<PC::Error>> {
        let supported_hiding_bound = 1; // we need to blind oracles for multiproof and opening in x3
        let (committer_key, verifier_key) =
            PC::trim(srs, srs.max_degree(), supported_hiding_bound, None)
                .map_err(Error::from_pc_err)?;

        Ok((committer_key, verifier_key))
    }

    fn prove<'a, R: Rng>(
        pk: &ProverKey<F, PC>,
        preprocessed: &ProverPreprocessedInput<F, PC>,
        witness_oracles: &'a mut [WitnessProverOracle<F>],
        instance_oracles: &'a mut [InstanceProverOracle<F>],
        vos: &[&'a dyn VirtualOracle<F>], // TODO: this should be in index
        domain_size: usize,
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
            preprocessed,
        );

        let verifier_init_state = PIOPforPolyIdentity::<F, PC>::init_verifier();

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
            .flat_map(|(_, _, a_prime, s_prime)| vec![a_prime, s_prime]);

        let lookup_prime_labeled: Vec<
            LabeledPolynomial<F, DensePolynomial<F>>,
        > = lookup_polys
            .iter()
            .flat_map(|(_, _, a_prime, s_prime)| {
                vec![a_prime.to_labeled(), s_prime.to_labeled()]
            })
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
                preprocessed,
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
            witness_oracles,
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

        oracles.extend_from_slice(preprocessed_oracles.as_slice());

        let oracle_rands: Vec<PC::Randomness> = wtns_rands
            .iter()
            .chain(lookup_rands.iter())
            .chain(lookup_z_rands.iter())
            .chain(quotient_rands.iter())
            .chain(z_rands.iter())
            .chain(preprocessed.empty_rands_for_fixed.iter())
            .cloned()
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

        let mut quotient_eval = F::zero();
        let evaluate_vo = |vo: &&dyn VirtualOracle<F>, c: F| {
            let vo_evaluation = vo.get_expression().evaluate(
                &|x: F| x,
                &|query| {
                    let challenge = query.rotation.compute_evaluation_point(
                        c,
                        &omegas,
                    );
                    match query.oracle_type {
                        OracleType::Witness => {
                            match prover_state.witness_oracles_mapping.get(&query.label) {
                                Some(index) => prover_state.witness_oracles[*index].query(&challenge),
                                None => panic!("Witness oracle with label add_label not found")
                            }
                        },
                        OracleType::Instance => {
                            match prover_state.instance_oracles_mapping.get(&query.label) {
                                Some(index) => prover_state.instance_oracles[*index].query(&challenge),
                                None => panic!("Instance oracle with label {} not found", query.label)
                            }
                        },
                        OracleType::Fixed => {
                            match prover_state.fixed_oracles_mapping.get(&query.label) {
                                Some(index) => preprocessed.fixed_oracles[*index].query(&challenge),
                                None => panic!("Fixed oracle with label add_label not found")
                            }
                        },
                    }
                },
                &|x: F| -x,
                &|x: F, y: F| x + y,
                &|x: F, y: F| x * y,
                &|x: F, y: F| x * y,
            );
            vo_evaluation
        };
        // Check all VOs expressions are 0 in ALL the domain. If some other vanishing poly is being
        // used this check may fail and the proof could still be valid!
        for (row_n, omega) in omegas.iter().enumerate() {
            for (vo_index, vo) in vos.iter().enumerate() {
                let vo_evaluation = evaluate_vo(vo, *omega);

                if vo_evaluation != F::zero() {
                    panic!("VO number {} failed at row {}", vo_index, row_n);
                }
            }
        }

        /* END SANITY CHECK BEFORE INVOKING VERIFIER */

        Ok(proof)
    }
    #[allow(clippy::too_many_arguments)]
    fn verify(
        vk: &VerifierKey<F, PC>,
        preprocessed: &mut VerifierPreprocessedInput<F, PC>,
        proof: Proof<F, PC>,
        witness_oracles: &mut [WitnessVerifierOracle<F, PC>],
        instance_oracles: &mut [InstanceVerifierOracle<F>],
        vos: &[&dyn VirtualOracle<F>],
        domain_size: usize,
        vanishing_polynomial: &DensePolynomial<F>,
    ) -> Result<(), Error<PC::Error>> {
        Ok(())
    }
}
