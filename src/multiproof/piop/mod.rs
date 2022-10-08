use std::{
    collections::{BTreeMap, BTreeSet},
    iter::{self, successors},
    marker::PhantomData,
};

use ark_ff::{to_bytes, PrimeField, Zero};
use ark_poly::{
    univariate::DensePolynomial, EvaluationDomain, GeneralEvaluationDomain,
    Polynomial,
};
use ark_poly_commit::{
    evaluate_query_set, LabeledCommitment, LabeledPolynomial,
};
use ark_std::rand::{Rng, RngCore};

use crate::{
    commitment::HomomorphicCommitment,
    concrete_oracle::{CommittedConcreteOracle, InstantiableConcreteOracle},
    rng::FiatShamirRng,
    vo::query::Rotation,
};

use super::{
    error::Error,
    poly::{construct_lagrange_basis, construct_vanishing},
    Proof,
};

pub mod prover;
pub mod verifier;

// use super::error::Error;

pub struct PIOP<F: PrimeField> {
    _f: PhantomData<F>,
}
#[derive(Debug)]
pub enum PIOPError {}

pub struct Multiopen<
    F: PrimeField,
    PC: HomomorphicCommitment<F>,
    FS: FiatShamirRng,
> {
    _f: PhantomData<F>,
    _pc: PhantomData<PC>,
    _fs: PhantomData<FS>,
}

// TODO: since polynomials are masked by hand rands(blinds) are omitted here
// however revisit this part, consider sending rands even if they are empty(for modularity)
// and accumulate rands when computing aggregate q_commitments

// TODO: revisit PIOP transcript handling again with two possibilities
// a) Current Version - Send &mut fs_rng that already absorbed (vk, commitments, evaluations) and start squeezing x1, x2
// b) For modularity start with empty fs_rng and absorb (vk, commitments, evaluations) again
impl<F: PrimeField, PC: HomomorphicCommitment<F>, FS: FiatShamirRng>
    Multiopen<F, PC, FS>
{
    pub const PROTOCOL_NAME: &'static [u8] = b"GEOMETRY-MULTIOPEN";

    pub fn prove<'a>(
        ck: &PC::CommitterKey,
        oracles: &[InstantiableConcreteOracle<F>],
        evaluation_challenge: F,
        domain_size: usize,
        fs_rng: &mut FS,
    ) -> Result<Proof<F, PC>, Error<PC::Error>> {
        // let labeled_oracles: Vec<LabeledPolynomial<F, DensePolynomial<F>>> = oracles.iter().map(|oracle| oracle.to_labeled()).collect();

        // let (oracles_commitments, _) =
        //     PC::commit(ck, &labeled_oracles, None).map_err(Error::from_pc_err)?;

        let verifier_state = PIOP::init_verifier(evaluation_challenge);

        // let mut fs_rng =
        //     FS::initialize(&to_bytes![&Self::PROTOCOL_NAME, evals].unwrap()); // TODO: add &pk.vk, &commitments and evaluation_challenge?

        let (verifier_state, verifier_first_msg) =
            PIOP::verifier_first_round(verifier_state, fs_rng);

        let prover_state = PIOP::init_prover(oracles, domain_size)
            .map_err(Error::from_piop_err)?;

        let (f_agg_poly, prover_state) = PIOP::prover_first_round(
            prover_state,
            evaluation_challenge,
            &verifier_first_msg,
        )
        .map_err(Error::from_piop_err)?;

        let (f_agg_poly_commitment, _) =
            PC::commit(ck, iter::once(&f_agg_poly), None).map_err(Error::from_pc_err)?;

        fs_rng.absorb(&to_bytes![&f_agg_poly_commitment].unwrap());

        let (verifier_state, verifier_second_msg) =
            PIOP::verifier_second_round(verifier_state, fs_rng);

        let q_evals =
            PIOP::prover_second_round(&prover_state, &verifier_second_msg)
                .map_err(Error::from_piop_err)?;

        fs_rng.absorb(&to_bytes![q_evals].unwrap());

        let (_, verifier_third_msg) =
            PIOP::verifier_third_round(verifier_state, fs_rng);

        let final_poly = PIOP::prover_third_round(&prover_state, &verifier_third_msg).map_err(Error::from_piop_err)?;

        let (final_poly_commitment, rands) =
            PC::commit(ck, iter::once(&final_poly), None)
                .map_err(Error::from_pc_err)?;

        let opening_proof = PC::open(
            ck,
            iter::once(&final_poly),
            final_poly_commitment.clone().iter(),
            &verifier_second_msg.x3,
            F::one(), // Opening challenge is not needed since only one polynomial is being committed
            rands.iter(),
            None, // Randomness is not needed since only one polynomial is committed
        )
        .map_err(Error::from_pc_err)?;

        let proof = Proof {
            q_evals,
            f_commit: f_agg_poly_commitment[0].commitment().clone(),
            opening_proof,
        };

        Ok(proof)
    }

    pub fn verify(
        vk: &PC::VerifierKey,
        proof: Proof<F, PC>,
        oracles: &[CommittedConcreteOracle<F, PC>], // At this moment challenge -> eval mapping should already be filled
        evaluation_challenge: F,
        domain_size: usize,
        fs_rng: &mut FS,
    ) -> Result<(), Error<PC::Error>> {
        let domain = GeneralEvaluationDomain::new(domain_size).unwrap();
        let verifier_state = PIOP::init_verifier(evaluation_challenge);

        // let mut fs_rng =
        //     FS::initialize(&to_bytes![&Self::PROTOCOL_NAME, evals].unwrap()); // TODO: add &pk.vk, &commitments and evaluation_challenge

        let (verifier_state, verifier_first_msg) =
            PIOP::verifier_first_round(verifier_state, fs_rng);

        fs_rng.absorb(&to_bytes![proof.f_commit].unwrap());

        let (verifier_state, verifier_second_msg) =
            PIOP::verifier_second_round(verifier_state, fs_rng);

        fs_rng.absorb(&to_bytes![proof.q_evals].unwrap());

        let (_, verifier_third_msg) =
            PIOP::verifier_third_round(verifier_state, fs_rng);

        let mut opening_sets = BTreeMap::<
            BTreeSet<Rotation>,
            Vec<&CommittedConcreteOracle<F, PC>>,
        >::new();

        for oracle in oracles.iter() {
            let oracles = opening_sets
                .entry(oracle.queried_rotations.clone())
                .or_insert(vec![]);
            oracles.push(oracle)
        }

        // Max number of oracles in one opening set are all oracles
        let x1_powers: Vec<F> = successors(Some(F::one()), |x1_i| {
            Some(*x1_i * verifier_first_msg.x1)
        })
        .take(oracles.len())
        .collect();

        let qs = opening_sets.iter().map(|(rotations, oracles)| {
            let mut q_i = PC::zero_comm();
            let mut q_i_evals_set = BTreeMap::<F, F>::new();

            for (i, &oracle) in oracles.iter().enumerate() {
                q_i = PC::add(
                    &q_i,
                    &PC::scale_com(oracle.get_commitment(), x1_powers[i]),
                );
            }

            let omegas: Vec<F> = domain.elements().collect();
            for rotation in rotations {
                let evaluation_point = rotation
                    .compute_evaluation_point(evaluation_challenge, &omegas);
                let mut evaluation = F::zero();
                for (i, &oracle) in oracles.iter().enumerate() {
                    evaluation += x1_powers[i]
                        * oracle.query_at_challenge(&evaluation_point);
                }

                let prev = q_i_evals_set.insert(evaluation_point, evaluation);
                if prev.is_some() {
                    panic!("Same evaluation point for different rotations")
                }
            }

            (q_i, q_i_evals_set)
        });

        let f_evals: Vec<F> = qs
            .clone()
            .zip(proof.q_evals.iter())
            .map(|((_, q_eval_set), &q_eval)| {
                let evaluation_domain: Vec<F> =
                    q_eval_set.keys().cloned().collect();

                let z_h = construct_vanishing(&evaluation_domain);

                let lagrange_bases =
                    construct_lagrange_basis(&evaluation_domain);
                let r_evals: Vec<F> = q_eval_set.values().cloned().collect();

                let mut r_poly = DensePolynomial::zero();
                for (l_i, &r_i) in lagrange_bases.iter().zip(r_evals.iter()) {
                    r_poly += &(l_i * r_i)
                }

                (q_eval - r_poly.evaluate(&verifier_second_msg.x3))
                    * z_h.evaluate(&verifier_second_msg.x3).inverse().unwrap()
            })
            .collect();

        let x2_powers: Vec<F> = successors(Some(F::one()), |x2_i| {
            Some(*x2_i * verifier_first_msg.x2)
        })
        .take(oracles.len())
        .collect();

        let mut final_poly_commitment = proof.f_commit.clone();
        let mut final_poly_eval = F::zero();
        for (i, &f_eval) in
            f_evals.iter().enumerate()
        {
            final_poly_eval += x2_powers[i] * f_eval;
        }

        let x4_powers: Vec<F> =
            successors(Some(verifier_third_msg.x4), |x4_i| {
                Some(*x4_i * verifier_third_msg.x4)
            })
            .take(proof.q_evals.len())
            .collect();

        for (i, ((q_commitment, _), &q_eval)) in
            qs.zip(proof.q_evals.iter()).enumerate()
        {
            final_poly_commitment = PC::add(
                &final_poly_commitment,
                &PC::scale_com(&q_commitment, x4_powers[i]),
            );
            final_poly_eval += x4_powers[i] * q_eval;
        }

        let final_poly_commitment = LabeledCommitment::new(
            "final_poly".to_string(),
            final_poly_commitment,
            None,
        );

        let res = PC::check(
            vk,
            &[final_poly_commitment],
            &verifier_second_msg.x3,
            [final_poly_eval],
            &proof.opening_proof,
            F::one(),
            None,
        )
        .map_err(Error::from_pc_err)?;

        if !res {
            return Err(Error::OpeningCheckFailed);
        }

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use std::collections::{BTreeMap, BTreeSet};

    use crate::{
        commitment::KZG10,
        concrete_oracle::{
            CommittedConcreteOracle, InstantiableConcreteOracle, OracleType,
        },
        rng::{SimpleHashFiatShamirRng, FiatShamirRng},
        vo::query::Rotation,
    };
    use ark_bls12_381::{Bls12_381, Fr as F};
    use ark_ff::to_bytes;
    use ark_poly::{
        univariate::DensePolynomial, EvaluationDomain, GeneralEvaluationDomain,
        Polynomial, UVPolynomial,
    };
    use ark_poly_commit::{
        LabeledPolynomial, PCUniversalParams, PolynomialCommitment,
    };
    use ark_std::test_rng;
    use blake2::Blake2s;
    use rand_chacha::ChaChaRng;

    use super::Multiopen;
    type FS = SimpleHashFiatShamirRng<Blake2s, ChaChaRng>;

    type PC = KZG10<Bls12_381>;
    type MultiopenInst = Multiopen<F, PC, FS>;

    #[test]
    fn test_halo2_book_example() {
        let max_degree = 30;
        let mut rng = test_rng();

        let domain_size = 16;
        let domain = GeneralEvaluationDomain::<F>::new(domain_size).unwrap();
        let poly_degree = domain_size - 1;

        let srs = PC::setup(max_degree, None, &mut rng).unwrap();

        let (committer_key, verifier_key) =
            PC::trim(&srs, srs.max_degree(), 0, None).unwrap();

        let a_poly = DensePolynomial::<F>::rand(poly_degree, &mut rng);
        let b_poly = DensePolynomial::<F>::rand(poly_degree, &mut rng);

        let c_poly = DensePolynomial::<F>::rand(poly_degree, &mut rng);
        let d_poly = DensePolynomial::<F>::rand(poly_degree, &mut rng);

        let a = InstantiableConcreteOracle {
            label: "a".to_string(),
            poly: a_poly.clone(),
            evals_at_coset_of_extended_domain: None,
            oracle_type: OracleType::Witness,
            queried_rotations: BTreeSet::from([Rotation::curr()]),
            should_mask: false,
        };

        let b = InstantiableConcreteOracle {
            label: "b".to_string(),
            poly: b_poly.clone(),
            evals_at_coset_of_extended_domain: None,
            oracle_type: OracleType::Witness,
            queried_rotations: BTreeSet::from([Rotation::curr()]),
            should_mask: false,
        };

        let c = InstantiableConcreteOracle {
            label: "c".to_string(),
            poly: c_poly.clone(),
            evals_at_coset_of_extended_domain: None,
            oracle_type: OracleType::Witness,
            queried_rotations: BTreeSet::from([
                Rotation::curr(),
                Rotation::next(),
            ]),
            should_mask: false,
        };

        let d = InstantiableConcreteOracle {
            label: "d".to_string(),
            poly: d_poly.clone(),
            evals_at_coset_of_extended_domain: None,
            oracle_type: OracleType::Witness,
            queried_rotations: BTreeSet::from([
                Rotation::curr(),
                Rotation::next(),
            ]),
            should_mask: false,
        };

        let oracles = [a, b, c, d];

        let labeled_oracles: Vec<LabeledPolynomial<F, DensePolynomial<F>>> =
            oracles.iter().map(|oracle| oracle.to_labeled()).collect();
        let (oracles_commitments, _) =
            PC::commit(&committer_key, &labeled_oracles, None).unwrap();

        let xi = F::from(13131u64);
        let omega = domain.element(1);

        let omega_xi = omega * xi;

        let a_at_xi = a_poly.evaluate(&xi);
        let b_at_xi = b_poly.evaluate(&xi);
        let c_at_xi = c_poly.evaluate(&xi);
        let d_at_xi = d_poly.evaluate(&xi);
        let c_at_omega_xi = c_poly.evaluate(&omega_xi);
        let d_at_omega_xi = d_poly.evaluate(&omega_xi);

        let evals = vec![
            a_at_xi,
            b_at_xi,
            c_at_xi,
            d_at_xi,
            c_at_omega_xi,
            c_at_omega_xi,
            d_at_omega_xi,
        ];

        let a_ver = CommittedConcreteOracle {
            label: "a".to_string(),
            queried_rotations: BTreeSet::from([Rotation::curr()]),
            should_mask: false,
            evals_at_challenges: BTreeMap::from([(xi, a_at_xi)]),
            commitment: Some(oracles_commitments[0].commitment().clone()),
        };

        let b_ver = CommittedConcreteOracle {
            label: "b".to_string(),
            queried_rotations: BTreeSet::from([Rotation::curr()]),
            should_mask: false,
            evals_at_challenges: BTreeMap::from([(xi, b_at_xi)]),
            commitment: Some(oracles_commitments[1].commitment().clone()),
        };

        let c_ver = CommittedConcreteOracle {
            label: "c".to_string(),
            queried_rotations: BTreeSet::from([
                Rotation::curr(),
                Rotation::next(),
            ]),
            should_mask: false,
            evals_at_challenges: BTreeMap::from([
                (xi, c_at_xi),
                (omega_xi, c_at_omega_xi),
            ]),
            commitment: Some(oracles_commitments[2].commitment().clone()),
        };

        let d_ver = CommittedConcreteOracle {
            label: "d".to_string(),
            queried_rotations: BTreeSet::from([
                Rotation::curr(),
                Rotation::next(),
            ]),
            should_mask: false,
            evals_at_challenges: BTreeMap::from([
                (xi, d_at_xi),
                (omega_xi, d_at_omega_xi),
            ]),
            commitment: Some(oracles_commitments[3].commitment().clone()),
        };

        let ver_oracles = [a_ver, b_ver, c_ver, d_ver];

        let mut fs_rng =
            FS::initialize(&to_bytes![&oracles_commitments, &evals, &xi].unwrap());

        let proof = MultiopenInst::prove(
            &committer_key,
            &oracles,
            xi,
            domain_size,
            &mut fs_rng
        )
        .unwrap();

        let mut fs_rng =
        FS::initialize(&to_bytes![&oracles_commitments, &evals, &xi].unwrap());

        let res = MultiopenInst::verify(
            &verifier_key,
            proof,
            &ver_oracles,
            xi,
            domain_size,
            &mut fs_rng
        );

        assert_eq!(res.is_ok(), true);
    }
}