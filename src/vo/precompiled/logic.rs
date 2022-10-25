use super::PrecompiledVO;
use crate::{
    oracles::{query::OracleType, rotation::Rotation},
    vo::{query::VirtualQuery, virtual_expression::VirtualExpression},
};
use ark_ff::PrimeField;

// Precompiled VOs related to 4-wire LogicGate

/// Delta VO is used to check the decomposition of a value in 2-bit increments.
/// An n-bit value a: a_0, a_1, ..., a_n, where a_0 is the most significant bit
/// will be split in 2-bit values and then stored as an accumulator.
/// In this way, the first cell of the wire will store the value of the first
/// (most significant) 2 bits, and the last cell will store the value a.
/// The value of intermediate cells will be: the previous cell value * 4 + the
/// value of the new 2-bit value.
/// This accumulation relation is the one enforced by Delta:
/// 0 <= (a_next - 4 * a) < 4
pub struct Delta {}

impl<F: PrimeField> PrecompiledVO<F> for Delta {
    fn get_expr_and_queries() -> (VirtualExpression<F>, Vec<VirtualQuery>) {
        // Witnesses
        let a = VirtualQuery::new(0, Rotation::curr(), OracleType::Witness);
        let a_next =
            VirtualQuery::new(0, Rotation::next(), OracleType::Witness);

        // Fixed
        let q_last = VirtualQuery::new(0, Rotation::curr(), OracleType::Fixed);
        let expr = {
            let a: VirtualExpression<F> = a.clone().into();
            let a_next: VirtualExpression<F> = a_next.clone().into();

            let q_last: VirtualExpression<F> = q_last.clone().into();
            let q_not_last = VirtualExpression::Constant(F::one()) - q_last;

            let const_4: VirtualExpression<F> =
                VirtualExpression::Constant(F::from(4u32));
            let delta = |e: VirtualExpression<F>| -> VirtualExpression<F> {
                let const_1: VirtualExpression<F> =
                    VirtualExpression::Constant(F::one());
                let const_2: VirtualExpression<F> =
                    VirtualExpression::Constant(F::from(2u32));
                let const_3: VirtualExpression<F> =
                    VirtualExpression::Constant(F::from(3u32));
                (e.clone() - const_3)
                    * (e.clone() - const_2)
                    * (e.clone() - const_1)
                    * e
            };
            q_not_last * delta(a_next - const_4 * a)
        };

        (expr, vec![q_last, a, a_next])
    }
}

/// DeltaXorAnd VO is used to to perform a bitwise XOR or AND operation
/// between 2 2-bit values. It uses a fixed selector (q_c) to select the
/// operation:
///    - XOR: q_c = -1
///    - AND: q_c = 1
/// It also uses an extra witness that must hold the product of the 2 inputs.
/// The constraint is G = 0 where:
/// ```text
/// G = H + E
/// H = qc * [9c - 3(a+b)]
/// E = 3(a+b+d) - 2F
/// F = c[c(4c - 18(a+b) + 81) + 18(a^2 + b^2) - 81(a+b) + 83]
/// ```
/// where a and b are the 2-bit inputs,
/// c is their product a*b
/// and d is the result of the logic operation: a (& or ^) b
pub struct DeltaXorAnd {}

impl<F: PrimeField> PrecompiledVO<F> for DeltaXorAnd {
    // TODO: When the full arbitrary number of bit implementation is done
    // the inputs a, b and output d must be modified to work with the accumulated
    // results. This involves an extra query at the next rotation and a sustitution:
    // a => (a_next - 4 * a_curr) ... same for b and d.
    fn get_expr_and_queries() -> (VirtualExpression<F>, Vec<VirtualQuery>) {
        // Witnesses
        let a = VirtualQuery::new(0, Rotation::curr(), OracleType::Witness);
        let b = VirtualQuery::new(1, Rotation::curr(), OracleType::Witness);
        let c = VirtualQuery::new(2, Rotation::curr(), OracleType::Witness);
        let d = VirtualQuery::new(2, Rotation::curr(), OracleType::Witness);
        // Selector
        let qc = VirtualQuery::new(0, Rotation::curr(), OracleType::Fixed);

        let expr = {
            let qc: VirtualExpression<F> = qc.clone().into();

            let a: VirtualExpression<F> = a.clone().into();
            let b: VirtualExpression<F> = b.clone().into();
            let c: VirtualExpression<F> = c.clone().into();
            let d: VirtualExpression<F> = d.clone().into();

            let const_2: VirtualExpression<F> =
                VirtualExpression::Constant(F::from(2u32));
            let const_3: VirtualExpression<F> =
                VirtualExpression::Constant(F::from(3u32));
            let const_4: VirtualExpression<F> =
                VirtualExpression::Constant(F::from(4u32));
            let const_9: VirtualExpression<F> =
                VirtualExpression::Constant(F::from(9u32));
            let const_18: VirtualExpression<F> =
                VirtualExpression::Constant(F::from(18u32));
            let const_81: VirtualExpression<F> =
                VirtualExpression::Constant(F::from(81u32));
            let const_83: VirtualExpression<F> =
                VirtualExpression::Constant(F::from(83u32));

            let f = c.clone()
                * (c.clone()
                    * (const_4 * c
                        - const_18.clone() * (a.clone() + b.clone())
                        + const_81.clone())
                    + const_18
                        * (a.clone() * a.clone() + b.clone() * b.clone())
                    - const_81 * (a.clone() + b.clone())
                    + const_83);
            let e = const_3.clone() * (a.clone() + b.clone() + d.clone())
                - const_2 * f;
            let h = qc * (const_9 * d - const_3 * (a + b));
            let a = h + e;
            a
        };

        (expr, vec![a, b, c, d, qc])
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use std::collections::{BTreeMap, BTreeSet};
    use std::iter::successors;

    use ark_bls12_381::{Bls12_381, Fr};
    use ark_ff::{One, Zero};

    use ark_poly::{
        univariate::DensePolynomial, EvaluationDomain, GeneralEvaluationDomain,
        UVPolynomial,
    };

    use ark_poly_commit::{LabeledPolynomial, PolynomialCommitment};
    use ark_serialize::CanonicalSerialize;
    use ark_std::rand::RngCore;
    use ark_std::test_rng;
    use rand_chacha::ChaChaRng;

    use crate::data_structures::{
        PermutationInfo, ProverKey, ProverPreprocessedInput,
        VerifierPreprocessedInput,
    };
    use crate::indexer::Indexer;

    use crate::oracles::fixed::{FixedProverOracle, FixedVerifierOracle};
    use crate::oracles::instance::{
        InstanceProverOracle, InstanceVerifierOracle,
    };

    use crate::oracles::witness::{WitnessProverOracle, WitnessVerifierOracle};
    use crate::rng::SimpleHashFiatShamirRng;
    use crate::vo::generic_vo::GenericVO;
    use crate::PIL;
    use blake2::Blake2s;

    use crate::commitment::{HomomorphicCommitment, KZG10};
    use crate::vo::VirtualOracle;

    use itertools::izip;

    type F = Fr;
    type FS = SimpleHashFiatShamirRng<Blake2s, ChaChaRng>;
    type PC = KZG10<Bls12_381>;

    type PilInstance = PIL<F, PC, FS>;

    #[test]
    fn test_delta() {
        let domain_size = 16;
        let poly_degree = domain_size - 1;
        let max_degree = poly_degree; // + max_blinding;

        let mut rng = test_rng();
        let srs = PilInstance::universal_setup(max_degree, &mut rng).unwrap();

        let (ck, verifier_key) = PilInstance::prepare_keys(&srs).unwrap();

        let domain = GeneralEvaluationDomain::<F>::new(domain_size).unwrap();

        let vals = &[F::zero(), F::one(), F::from(2u32), F::from(3u32)];
        let mut rand_4 = || {
            let u = rng.next_u32() % 4;
            vals[u as usize].clone()
        };

        let initial_val = rand_4();
        let a_evals: Vec<F> = successors(Some(initial_val), |v| {
            Some(rand_4() + F::from(4u32) * v)
        })
        .take(domain_size)
        .collect();

        let mut q_last_evals = vec![F::zero(); 16];
        q_last_evals[15] = F::one();

        // check
        let delta =
            |v| v * (v - F::one()) * (v - F::from(2u32)) * (v - F::from(3u32));
        for (i, &v) in a_evals.iter().enumerate() {
            if i < 15 {
                assert_eq!(F::zero(), delta(a_evals[i + 1] - F::from(4u32) * v))
            }
        }

        let a_poly =
            DensePolynomial::from_coefficients_slice(&domain.ifft(&a_evals));

        let q_last_poly = DensePolynomial::from_coefficients_slice(
            &domain.ifft(&q_last_evals),
        );

        let a = WitnessProverOracle {
            label: "a".to_string(),
            poly: a_poly,
            evals_at_coset_of_extended_domain: None,
            queried_rotations: BTreeSet::new(),
            should_permute: false,
            evals: a_evals.clone(),
        };

        let q_last = FixedProverOracle {
            label: "q_last".to_string(),
            poly: q_last_poly.clone(),
            evals: q_last_evals,
            evals_at_coset_of_extended_domain: None,
            queried_rotations: BTreeSet::new(),
        };

        let mut witness_oracles = [a];
        let mut instance_oracles: Vec<InstanceProverOracle<F>> = vec![];
        let mut fixed_oracles: Vec<FixedProverOracle<F>> = vec![q_last];

        let mut delta_vo = GenericVO::<F>::init(Delta::get_expr_and_queries());

        delta_vo.configure(
            &mut witness_oracles,
            &mut instance_oracles,
            &mut fixed_oracles,
        );

        let vos: Vec<&dyn VirtualOracle<F>> = vec![&delta_vo];

        let vk = Indexer::index(
            &verifier_key,
            &vos,
            vec![],
            &witness_oracles,
            &instance_oracles,
            &fixed_oracles,
            domain,
            &domain.vanishing_polynomial().into(),
            PermutationInfo::empty(),
            0,
        )
        .unwrap();

        let pk = ProverKey::from_ck_and_vk(&ck, &vk);

        let q_blind = FixedProverOracle {
            label: "q_blind".to_string(),
            poly: DensePolynomial::zero(),
            evals: vec![],
            evals_at_coset_of_extended_domain: None,
            queried_rotations: BTreeSet::default(),
        };

        let preprocessed = ProverPreprocessedInput::new(
            &fixed_oracles,
            &vec![],
            &vec![],
            &q_blind,
            &vk.index_info,
        );

        let proof = PilInstance::prove(
            &pk,
            &preprocessed,
            &mut witness_oracles,
            &mut instance_oracles,
            &vos,
            domain_size,
            &domain.vanishing_polynomial().into(),
            &mut rng,
        )
        .unwrap();

        println!("{}", proof.info());
        println!("{}", proof.cumulative_info());
        println!("in bytes: {}", proof.serialized_size());

        // Verifier
        // Repeat everything to make sure that we are not implicitly using something from prover

        let mut witness_ver_oracles: Vec<_> = ["a"]
            .into_iter()
            .map(|label| WitnessVerifierOracle {
                label: label.to_string(),
                queried_rotations: BTreeSet::new(),
                should_permute: false,
                evals_at_challenges: BTreeMap::default(),
                commitment: None,
            })
            .collect();

        let mut instance_oracles: Vec<InstanceVerifierOracle<F>> = vec![];
        let labeled_fixed: Vec<LabeledPolynomial<F, DensePolynomial<F>>> =
            vec![LabeledPolynomial::new(
                "q_last".to_string(),
                q_last_poly,
                None,
                None,
            )];

        let (fixed_comm, _) =
            PC::commit(&ck, labeled_fixed.iter(), None).unwrap();

        let mut fixed_oracles: Vec<_> = fixed_comm
            .into_iter()
            .map(|comm| FixedVerifierOracle::<F, PC> {
                label: comm.label().to_string(),
                queried_rotations: BTreeSet::default(),
                evals_at_challenges: BTreeMap::default(),
                commitment: Some(comm.commitment().clone()),
            })
            .collect();

        let mut delta_vo = GenericVO::<F>::init(Delta::get_expr_and_queries());

        delta_vo.configure(
            &mut witness_ver_oracles,
            &mut instance_oracles,
            &mut fixed_oracles,
        );

        let vos: Vec<&dyn VirtualOracle<F>> = vec![&delta_vo];

        let mut vk = Indexer::index(
            &verifier_key,
            &vos,
            vec![],
            &witness_ver_oracles,
            &instance_oracles,
            &fixed_oracles,
            domain,
            &domain.vanishing_polynomial().into(),
            PermutationInfo::empty(),
            0,
        )
        .unwrap();

        let q_blind = FixedVerifierOracle {
            label: "q_blind".to_string(),
            queried_rotations: BTreeSet::default(),
            evals_at_challenges: BTreeMap::default(),
            commitment: Some(PC::zero_comm()),
        };

        let verifier_pp = VerifierPreprocessedInput {
            fixed_oracles: fixed_oracles.clone(),
            table_oracles: vec![],
            permutation_oracles: vec![],
            q_blind,
        };
        // We clone because fixed oracles must be mutable in order to add evals at challenge
        // Another option is to create reset method which will just reset challenge to eval mapping
        // This is anyway just mockup of frontend
        let mut pp_clone = verifier_pp.clone();

        let res = PilInstance::verify(
            &mut vk,
            &mut pp_clone,
            proof,
            &mut witness_ver_oracles,
            &mut instance_oracles,
            vos.as_slice(),
            domain_size,
            &domain.vanishing_polynomial().into(),
            &mut rng,
        )
        .unwrap();

        assert_eq!(res, ());
    }

    // TODO Fix test
    #[test]
    fn test_delta_xor_and() {
        let domain_size = 16;
        let poly_degree = domain_size - 1;
        let max_degree = poly_degree; // + max_blinding;

        let mut rng = test_rng();
        let srs = PilInstance::universal_setup(max_degree, &mut rng).unwrap();

        let (ck, verifier_key) = PilInstance::prepare_keys(&srs).unwrap();

        let domain = GeneralEvaluationDomain::<F>::new(domain_size).unwrap();

        let (m_one, one) = (-F::one(), F::one());

        let a_values_full = vec![
            0u64, 0u64, 0u64, 0u64, 1u64, 1u64, 1u64, 1u64, 2u64, 2u64, 2u64,
            2u64, 3u64, 3u64, 3u64, 3u64, 0u64, 0u64, 0u64, 0u64, 1u64, 1u64,
            1u64, 1u64, 2u64, 2u64, 2u64, 2u64, 3u64, 3u64, 3u64, 3u64,
        ];
        let b_values_full = vec![
            0u64, 1u64, 2u64, 3u64, 0u64, 1u64, 2u64, 3u64, 0u64, 1u64, 2u64,
            3u64, 0u64, 1u64, 2u64, 3u64, 0u64, 1u64, 2u64, 3u64, 0u64, 1u64,
            2u64, 3u64, 0u64, 1u64, 2u64, 3u64, 0u64, 1u64, 2u64, 3u64,
        ];

        let q_c_evals_full = vec![
            one, one, one, one, one, one, one, one, one, one, one, one, one,
            one, one, one, m_one, m_one, m_one, m_one, m_one, m_one, m_one,
            m_one, m_one, m_one, m_one, m_one, m_one, m_one, m_one, m_one,
        ];
        let a_values = &a_values_full[..32];
        let b_values = &b_values_full[..32];
        let q_c_evals = &q_c_evals_full[..32];

        let a_evals: Vec<_> = a_values.iter().map(|&v| F::from(v)).collect();
        let b_evals: Vec<_> = b_values.iter().map(|&v| F::from(v)).collect();

        let q_c_poly =
            DensePolynomial::from_coefficients_slice(&domain.ifft(&q_c_evals));

        let c_evals: Vec<_> = izip!(a_evals.clone(), b_evals.clone())
            .map(|(a, b)| a * b)
            .collect();
        let d_evals: Vec<_> = izip!(a_values, b_values)
            .enumerate()
            .map(|(i, (a, b))| {
                if i < 16 {
                    F::from(a & b)
                } else {
                    F::from(a ^ b)
                }
            })
            .collect();

        let _check: Vec<_> = izip!(
            a_evals.clone(),
            b_evals.clone(),
            c_evals.clone(),
            d_evals.clone(),
            q_c_evals
        )
        .map(|(a, b, c, d, qc)| {
            // Check function copied from zk-garage
            let original_func = |(a, b, w, c, q_c): (F, F, F, F, F)| -> F {
                let nine = F::from(9_u64);
                let two = F::from(2_u64);
                let three = F::from(3_u64);
                let four = F::from(4_u64);
                let eighteen = F::from(18_u64);
                let eighty_one = F::from(81_u64);
                let eighty_three = F::from(83_u64);
                let var_f = w
                    * (w * (four * w - eighteen * (a + b) + eighty_one)
                        + eighteen * (a * a + b * b)
                        - eighty_one * (a + b)
                        + eighty_three);
                let var_e = three * (a + b + c) - (two * var_f);
                let var_b = q_c * ((nine * c) - three * (a + b));
                var_b + var_e
            };

            // Check function in VOs expression
            let const_2 = F::from(2u32);
            let const_3 = F::from(3u32);
            let const_4 = F::from(4u32);
            let const_9 = F::from(9u32);
            let const_18 = F::from(18u32);
            let const_81 = F::from(81u32);
            let const_83 = F::from(83u32);
            let f = c.clone()
                * (c.clone()
                    * (const_4 * c
                        - const_18.clone() * (a.clone() + b.clone())
                        + const_81.clone())
                    + const_18
                        * (a.clone() * a.clone() + b.clone() * b.clone())
                    - const_81 * (a.clone() + b.clone())
                    + const_83);
            let e = const_3.clone() * (a.clone() + b.clone() + d.clone())
                - const_2 * f;
            let h = *qc * (const_9 * d - const_3 * (a + b));
            let res = h + e;

            assert_eq!(F::zero(), original_func((a, b, c, d, *qc)));
            assert_eq!(F::zero(), res);
        })
        .collect();

        let witness_polys: Vec<_> = [
            a_evals.clone(),
            b_evals.clone(),
            c_evals.clone(),
            d_evals.clone(),
        ]
        .iter()
        .map(|evals| {
            DensePolynomial::from_coefficients_slice(&domain.ifft(evals))
        })
        .collect();

        let mut and_xor_vo =
            GenericVO::<F>::init(DeltaXorAnd::get_expr_and_queries());

        let mut witness_oracles: Vec<_> = [
            (witness_polys[0].clone(), a_evals, "a"),
            (witness_polys[1].clone(), b_evals, "b"),
            (witness_polys[2].clone(), c_evals, "product"),
            (witness_polys[3].clone(), d_evals, "logic"),
        ]
        .into_iter()
        .map(|(poly, evals, label)| WitnessProverOracle::<F> {
            label: label.to_string(),
            poly,
            evals_at_coset_of_extended_domain: None,
            queried_rotations: BTreeSet::new(),
            should_permute: false,
            evals,
        })
        .collect();

        let mut instance_oracles: Vec<InstanceProverOracle<F>> = vec![];

        let mut fixed_oracles: Vec<_> = [(q_c_poly.clone(), q_c_evals, "qc")]
            .into_iter()
            .map(|(poly, evals, label)| FixedProverOracle::<F> {
                label: label.to_string(),
                evals: evals.to_vec(),
                poly,
                evals_at_coset_of_extended_domain: None,
                queried_rotations: BTreeSet::new(),
            })
            .collect();

        and_xor_vo.configure(
            &mut witness_oracles,
            &mut instance_oracles,
            &mut fixed_oracles,
        );

        let vos: Vec<&dyn VirtualOracle<F>> = vec![&and_xor_vo];

        let vk = Indexer::index(
            &verifier_key,
            &vos,
            vec![],
            &witness_oracles,
            &instance_oracles,
            &fixed_oracles,
            domain,
            &domain.vanishing_polynomial().into(),
            PermutationInfo::empty(),
            0,
        )
        .unwrap();

        let pk = ProverKey::from_ck_and_vk(&ck, &vk);

        let q_blind = FixedProverOracle {
            label: "q_blind".to_string(),
            poly: DensePolynomial::zero(),
            evals: vec![],
            evals_at_coset_of_extended_domain: None,
            queried_rotations: BTreeSet::default(),
        };

        let preprocessed = ProverPreprocessedInput::new(
            &fixed_oracles,
            &vec![],
            &vec![],
            &q_blind,
            &vk.index_info,
        );
        let proof = PilInstance::prove(
            &pk,
            &preprocessed,
            &mut witness_oracles,
            &mut instance_oracles,
            &vos,
            domain_size,
            &domain.vanishing_polynomial().into(),
            &mut rng,
        )
        .unwrap();

        println!("{}", proof.info());
        println!("{}", proof.cumulative_info());
        println!("in bytes: {}", proof.serialized_size());

        // Verifier
        // Repeat everything to make sure that we are not implicitly using something from prover

        let mut witness_ver_oracles: Vec<_> = ["a", "b", "product", "logic"]
            .into_iter()
            .map(|label| WitnessVerifierOracle {
                label: label.to_string(),
                queried_rotations: BTreeSet::new(),
                should_permute: false,
                evals_at_challenges: BTreeMap::default(),
                commitment: None,
            })
            .collect();

        let mut instance_oracles: Vec<InstanceVerifierOracle<F>> = vec![];

        let labeled_fixed: Vec<LabeledPolynomial<F, DensePolynomial<F>>> =
            [(q_c_poly.clone(), "qc")]
                .iter()
                .map(|(poly, label)| {
                    LabeledPolynomial::new(
                        label.to_string(),
                        poly.clone(),
                        None,
                        None,
                    )
                })
                .collect();
        let (fixed_comm, _) =
            PC::commit(&ck, labeled_fixed.iter(), None).unwrap();

        let mut fixed_oracles: Vec<_> = fixed_comm
            .into_iter()
            .map(|comm| FixedVerifierOracle::<F, PC> {
                label: comm.label().to_string(),
                queried_rotations: BTreeSet::default(),
                evals_at_challenges: BTreeMap::default(),
                commitment: Some(comm.commitment().clone()),
            })
            .collect();

        let mut and_xor_vo =
            GenericVO::<F>::init(DeltaXorAnd::get_expr_and_queries());

        and_xor_vo.configure(
            &mut witness_ver_oracles,
            &mut instance_oracles,
            &mut fixed_oracles,
        );

        let vos: Vec<&dyn VirtualOracle<F>> = vec![&and_xor_vo];

        let mut vk = Indexer::index(
            &verifier_key,
            &vos,
            vec![],
            &witness_ver_oracles,
            &instance_oracles,
            &fixed_oracles,
            domain,
            &domain.vanishing_polynomial().into(),
            PermutationInfo::empty(),
            0,
        )
        .unwrap();

        let q_blind = FixedVerifierOracle {
            label: "q_blind".to_string(),
            queried_rotations: BTreeSet::default(),
            evals_at_challenges: BTreeMap::default(),
            commitment: Some(PC::zero_comm()),
        };

        let verifier_pp = VerifierPreprocessedInput {
            fixed_oracles: fixed_oracles.clone(),
            table_oracles: vec![],
            permutation_oracles: vec![],
            q_blind,
        };
        // We clone because fixed oracles must be mutable in order to add evals at challenge
        // Another option is to create reset method which will just reset challenge to eval mapping
        // This is anyway just mockup of frontend
        let mut pp_clone = verifier_pp.clone();

        let res = PilInstance::verify(
            &mut vk,
            &mut pp_clone,
            proof,
            &mut witness_ver_oracles,
            &mut instance_oracles,
            vos.as_slice(),
            domain_size,
            &domain.vanishing_polynomial().into(),
            &mut rng,
        )
        .unwrap();

        assert_eq!(res, ());
    }
}
