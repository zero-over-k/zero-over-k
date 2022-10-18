#[cfg(test)]
mod test {

    use std::collections::{BTreeMap, BTreeSet};

    use ark_bls12_381::{Bls12_381, Fr};
    use ark_ff::{One, UniformRand, Zero};
    use ark_poly::Polynomial;
    use ark_poly::{
        univariate::DensePolynomial, EvaluationDomain, GeneralEvaluationDomain,
        UVPolynomial,
    };

    use ark_poly_commit::{LabeledPolynomial, PolynomialCommitment};
    use ark_serialize::CanonicalSerialize;
    use ark_std::test_rng;
    use rand_chacha::ChaChaRng;

    use crate::data_structures::{
        ProverKey, ProverPreprocessedInput, VerifierPreprocessedInput,
    };
    use crate::indexer::Indexer;
    use crate::multiproof::poly;

    use crate::oracles::fixed::{FixedProverOracle, FixedVerifierOracle};
    use crate::oracles::instance::{
        InstanceProverOracle, InstanceVerifierOracle,
    };
    use crate::oracles::query;
    use crate::oracles::traits::Instantiable;
    use crate::oracles::witness::{WitnessProverOracle, WitnessVerifierOracle};
    use crate::rng::SimpleHashFiatShamirRng;
    use crate::vo::generic_vo::GenericVO;
    use crate::vo::precompiled_vos::{
        DeltaXorAnd, PrecompiledMul, PrecompiledPlonkArith, PrecompiledRescue,
        PrecompiledVO,
    };
    use crate::PIL;
    use blake2::Blake2s;

    use crate::commitment::KZG10;
    use crate::vo::VirtualOracle;

    use itertools::izip;

    type F = Fr;
    type FS = SimpleHashFiatShamirRng<Blake2s, ChaChaRng>;
    type PC = KZG10<Bls12_381>;

    type PilInstance = PIL<F, PC, FS>;

    #[test]
    fn test_simple_mul() {
        let domain_size = 16;
        let poly_degree = domain_size - 1;
        let max_degree = poly_degree;
        let mut rng = test_rng();

        let srs = PilInstance::universal_setup(max_degree, &mut rng).unwrap();

        let (ck, verifier_key) = PilInstance::prepare_keys(&srs).unwrap();

        let domain = GeneralEvaluationDomain::<F>::new(domain_size).unwrap();

        let a_poly = DensePolynomial::<F>::rand(poly_degree, &mut rng);
        let b_poly = DensePolynomial::<F>::rand(poly_degree, &mut rng);

        let a_evals = domain.fft(&a_poly);
        let b_evals = domain.fft(&b_poly);

        let c_evals = a_evals
            .iter()
            .zip(b_evals.iter())
            .map(|(&a, &b)| a * b)
            .collect::<Vec<_>>();

        let c_poly =
            DensePolynomial::from_coefficients_slice(&domain.ifft(&c_evals));

        for elem in domain.elements() {
            assert_eq!(
                a_poly.evaluate(&elem) * b_poly.evaluate(&elem)
                    - c_poly.evaluate(&elem),
                F::zero()
            );
        }

        let a = WitnessProverOracle {
            label: "a".to_string(),
            poly: a_poly,
            evals_at_coset_of_extended_domain: None,
            queried_rotations: BTreeSet::new(),
            should_permute: false,
            evals: a_evals,
        };

        let b = WitnessProverOracle {
            label: "b".to_string(),
            poly: b_poly,
            evals_at_coset_of_extended_domain: None,
            queried_rotations: BTreeSet::new(),
            should_permute: false,
            evals: b_evals,
        };

        let c = InstanceProverOracle {
            label: "c".to_string(),
            poly: c_poly.clone(),
            evals_at_coset_of_extended_domain: None,
            queried_rotations: BTreeSet::new(),
            evals: c_evals.clone(),
        };

        let mut mul_vo =
            GenericVO::<F, PC>::init(PrecompiledMul::get_expr_and_queries());

        let mut witness_oracles = [a, b];
        let mut instance_oracles = [c];
        let mut fixed_oracles: [FixedProverOracle<F>; 0] = [];

        mul_vo.configure(
            &mut witness_oracles,
            &mut instance_oracles,
            &mut fixed_oracles,
        );

        let vos: Vec<&dyn VirtualOracle<F>> = vec![&mul_vo];

        let vk = Indexer::index(
            &verifier_key,
            &vos,
            &witness_oracles,
            &instance_oracles,
            &fixed_oracles,
            domain,
            &domain.vanishing_polynomial().into(),
        )
        .unwrap();

        let pk = ProverKey::from_ck_and_vk(&ck, &vk);

        let preprocessed = ProverPreprocessedInput {
            fixed_oracles: vec![],
            permutation_oracles: vec![],
            empty_rands_for_fixed: vec![],
        };

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

        // Verifier
        let a_ver = WitnessVerifierOracle {
            label: "a".to_string(),
            queried_rotations: BTreeSet::default(),
            should_permute: false,
            evals_at_challenges: BTreeMap::default(),
            commitment: None,
        };

        let b_ver = WitnessVerifierOracle {
            label: "b".to_string(),
            queried_rotations: BTreeSet::default(),
            should_permute: false,
            evals_at_challenges: BTreeMap::default(),
            commitment: None,
        };

        // Repeat just to make sure some change from prover does not affect this
        let c = InstanceVerifierOracle {
            label: "c".to_string(),
            poly: c_poly.clone(),
            evals: c_evals.clone(),
            queried_rotations: BTreeSet::new(),
        };

        let mut ver_wtns_oracles = [a_ver, b_ver];
        let mut instance_oracles = [c];
        let mut fixed_oracles: [FixedVerifierOracle<F, PC>; 0] = [];

        let mut mul_vo =
            GenericVO::<F, PC>::init(PrecompiledMul::get_expr_and_queries());

        mul_vo.configure(
            &mut ver_wtns_oracles,
            &mut instance_oracles,
            &mut fixed_oracles,
        );

        let vos: Vec<&dyn VirtualOracle<F>> = vec![&mul_vo];

        // Repeat but this time provide verifier witness oracles
        let mut vk = Indexer::index(
            &verifier_key,
            &vos,
            &mut ver_wtns_oracles,
            &instance_oracles,
            &fixed_oracles,
            domain,
            &domain.vanishing_polynomial().into(),
        )
        .unwrap();

        let preprocessed = VerifierPreprocessedInput {
            fixed_oracles: vec![],
            permutation_oracles: vec![],
        };

        // Since we mutate fixed oracles by adding evals at challenge for specific proof
        // preprocessed input is cloned in order to enable preserving original preprocessed
        // Second option is just to "reset" preprocessed after verification ends
        let mut pp_clone = preprocessed.clone();

        let res = PilInstance::verify(
            &mut vk,
            &mut pp_clone,
            proof,
            &mut ver_wtns_oracles,
            &mut instance_oracles,
            &vos,
            domain_size,
            &domain.vanishing_polynomial().into(),
            &mut rng,
        )
        .unwrap();

        assert_eq!(res, ());
    }

    #[test]
    fn test_rescue_gate() {
        let max_degree = 15;
        let mut rng = test_rng();

        let srs = PilInstance::universal_setup(max_degree, &mut rng).unwrap();

        let (ck, verifier_key) = PilInstance::prepare_keys(&srs).unwrap();

        let domain_size = 16;
        let poly_degree = domain_size - 1;
        let domain = GeneralEvaluationDomain::<F>::new(domain_size).unwrap();

        let witness_polys: Vec<_> = (0..=4)
            .map(|_| DensePolynomial::<F>::rand(poly_degree, &mut rng))
            .collect();
        let witness_evals: Vec<Vec<F>> =
            witness_polys.iter().map(|poly| domain.fft(&poly)).collect();

        let selector_polys: Vec<_> = (0..=3)
            .map(|_| DensePolynomial::<F>::rand(poly_degree, &mut rng))
            .collect();
        let fixed_evals: Vec<Vec<F>> = selector_polys
            .iter()
            .map(|poly| domain.fft(&poly))
            .collect();

        let pow_5 = |v: &F| *v * v * v * v * v;
        let w5_evals: Vec<F> = izip!(
            &witness_evals[0],
            &witness_evals[1],
            &witness_evals[2],
            &witness_evals[3],
            &witness_evals[4],
            &fixed_evals[0],
            &fixed_evals[1],
            &fixed_evals[2],
            &fixed_evals[3],
        )
        .map(|(w1, w2, w3, w4, _w5, &q1, &q2, &q3, &q4)| {
            q1 * pow_5(w1) + q2 * pow_5(w2) + q3 * pow_5(w3) + q4 * pow_5(w4)
            // - pow_5(w5) //TODO: should this value be here
        })
        .collect();

        let w5_poly =
            DensePolynomial::from_coefficients_slice(&domain.ifft(&w5_evals));

        let mut rescue_vo =
            GenericVO::<F, PC>::init(PrecompiledRescue::get_expr_and_queries());

        let mut witness_oracles: Vec<_> = [
            (witness_polys[0].clone(), witness_evals[0].clone(), "a"),
            (witness_polys[1].clone(), witness_evals[1].clone(), "b"),
            (witness_polys[2].clone(), witness_evals[2].clone(), "c"),
            (witness_polys[3].clone(), witness_evals[3].clone(), "d"),
            (w5_poly, w5_evals.clone(), "e"),
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

        let mut instance_oracles = vec![];

        let mut selector_oracles: Vec<_> = [
            (selector_polys[0].clone(), "q1"),
            (selector_polys[1].clone(), "q2"),
            (selector_polys[2].clone(), "q3"),
            (selector_polys[3].clone(), "q4"),
        ]
        .into_iter()
        .map(|(poly, label)| FixedProverOracle::<F> {
            label: label.to_string(),
            evals: domain.fft(&poly),
            poly,
            evals_at_coset_of_extended_domain: None,
            queried_rotations: BTreeSet::new(),
        })
        .collect();

        rescue_vo.configure(
            &mut witness_oracles,
            &mut instance_oracles,
            &mut selector_oracles,
        );

        // q_expr[0].clone() * pow_5(&w_expr[0])
        // + q_expr[1].clone() * pow_5(&w_expr[1])
        // + q_expr[2].clone() * pow_5(&w_expr[2])
        // + q_expr[3].clone() * pow_5(&w_expr[3])
        // - w_expr[4].clone()
        for elem in domain.elements() {
            let q1 = selector_oracles[0].polynomial().evaluate(&elem);
            let q2 = selector_oracles[1].polynomial().evaluate(&elem);
            let q3 = selector_oracles[2].polynomial().evaluate(&elem);
            let q4 = selector_oracles[3].polynomial().evaluate(&elem);

            let w1 = witness_oracles[0].polynomial().evaluate(&elem);
            let w2 = witness_oracles[1].polynomial().evaluate(&elem);
            let w3 = witness_oracles[2].polynomial().evaluate(&elem);
            let w4 = witness_oracles[3].polynomial().evaluate(&elem);
            let wpow5 = witness_oracles[4].polynomial().evaluate(&elem);

            let rescue = q1 * pow_5(&w1)
                + q2 * pow_5(&w2)
                + q3 * pow_5(&w3)
                + q4 * pow_5(&w4)
                - wpow5;

            assert_eq!(rescue, F::zero())
        }

        let vos: Vec<&dyn VirtualOracle<F>> = vec![&rescue_vo];

        let vk = Indexer::index(
            &verifier_key,
            &vos,
            &witness_oracles,
            &instance_oracles,
            &selector_oracles,
            domain,
            &domain.vanishing_polynomial().into(),
        )
        .unwrap();

        let pk = ProverKey::from_ck_and_vk(&ck, &vk);

        let preprocessed = ProverPreprocessedInput::new(
            &selector_oracles,
            &vec![],
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

        let mut witness_ver_oracles: Vec<_> = ["a", "b", "c", "d", "e"]
            .into_iter()
            .map(|label| WitnessVerifierOracle::<F, PC> {
                label: label.to_string(),
                queried_rotations: BTreeSet::new(),
                should_permute: false,
                evals_at_challenges: BTreeMap::default(),
                commitment: None,
            })
            .collect();

        let mut instance_oracles: [InstanceVerifierOracle<F>; 0] = [];

        let labeled_selectors: Vec<LabeledPolynomial<F, DensePolynomial<F>>> =
            [
                (selector_polys[0].clone(), "q1"),
                (selector_polys[1].clone(), "q2"),
                (selector_polys[2].clone(), "q3"),
                (selector_polys[3].clone(), "q4"),
            ]
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

        let (selector_commitments, _) =
            PC::commit(&ck, labeled_selectors.iter(), None).unwrap();

        let mut selector_oracles: Vec<_> = selector_commitments
            .iter()
            .map(|cmt| FixedVerifierOracle::<F, PC> {
                label: cmt.label().clone(),
                queried_rotations: BTreeSet::default(),
                evals_at_challenges: BTreeMap::default(),
                commitment: Some(cmt.commitment().clone()),
            })
            .collect();

        let mut rescue_vo =
            GenericVO::<F, PC>::init(PrecompiledRescue::get_expr_and_queries());

        rescue_vo.configure(
            &mut witness_ver_oracles,
            &mut instance_oracles,
            &mut selector_oracles,
        );

        let vk = Indexer::index(
            &verifier_key,
            &vos,
            &witness_ver_oracles,
            &instance_oracles,
            &selector_oracles,
            domain,
            &domain.vanishing_polynomial().into(),
        )
        .unwrap();

        let verifier_pp = VerifierPreprocessedInput {
            fixed_oracles: selector_oracles.clone(),
            permutation_oracles: vec![],
        };

        // We clone because fixed oracles must be mutable in order to add evals at challenge
        // Another option is to create reset method which will just reset challenge to eval mapping
        // This is anyway just mockup of frontend
        let mut pp_clone = verifier_pp.clone();

        let vos: Vec<&dyn VirtualOracle<F>> = vec![&rescue_vo];

        let res = PilInstance::verify(
            &vk,
            &mut pp_clone,
            proof,
            &mut witness_ver_oracles,
            &mut [],
            &vos,
            domain_size,
            &domain.vanishing_polynomial().into(),
            &mut rng,
        )
        .unwrap();

        assert_eq!(res, ());
    }

    #[test]
    fn test_plonk_arith() {
        let domain_size = 4;
        let poly_degree = domain_size - 1;
        let max_degree = poly_degree;
        let mut rng = test_rng();

        let srs = PilInstance::universal_setup(max_degree, &mut rng).unwrap();

        let (ck, verifier_key) = PilInstance::prepare_keys(&srs).unwrap();

        let domain = GeneralEvaluationDomain::<F>::new(domain_size).unwrap();

        /*
            a <- rand
            b <- rand
            pi <- rand

            c[0] = a * b
            c[1] = a + b
            c[2] = pi[2]
            c[3] = a * b

            rows:
                0 qm = 1, ql = 0, qr = 0, qo = -1, qpi = 0
                1 qm = 0, ql = 1, qr = 1, qo = -1, qpi = 0
                2 qm = 0, ql = 0, qr = 0, qo = 1, qpi = -pi[2]
                3 qm = 1, ql = 0, qr = 0, qo = -1, qpi = 0
        */

        let a_poly = DensePolynomial::<F>::rand(poly_degree, &mut rng);
        let b_poly = DensePolynomial::<F>::rand(poly_degree, &mut rng);

        let a_evals = domain.fft(&a_poly);
        let b_evals = domain.fft(&b_poly);

        let mut c_evals = vec![F::zero(); domain_size];

        let mut pi_evals = vec![F::zero(); domain_size];
        pi_evals[2] = F::rand(&mut rng);

        let mut qm_evals = vec![F::zero(); domain_size];
        let mut ql_evals = vec![F::zero(); domain_size];
        let mut qr_evals = vec![F::zero(); domain_size];
        let mut qo_evals = vec![F::zero(); domain_size];
        let mut qpi_evals = vec![F::zero(); domain_size];

        // row0
        c_evals[0] = a_evals[0] * b_evals[0];
        qm_evals[0] = F::one();
        qo_evals[0] = -F::one();

        // row1
        c_evals[1] = a_evals[1] + b_evals[1];
        ql_evals[1] = F::one();
        qr_evals[1] = F::one();
        qo_evals[1] = -F::one();

        //row2
        c_evals[2] = pi_evals[2];
        qpi_evals[2] = -pi_evals[2];

        //row3
        c_evals[3] = a_evals[3] * b_evals[3];
        qm_evals[3] = F::one();
        qo_evals[3] = -F::one();

        // Define oracles
        let c_poly =
            DensePolynomial::from_coefficients_slice(&domain.ifft(&c_evals));
        let pi_poly =
            DensePolynomial::from_coefficients_slice(&domain.ifft(&pi_evals));

        let qm_poly =
            DensePolynomial::from_coefficients_slice(&domain.ifft(&qm_evals));
        let ql_poly =
            DensePolynomial::from_coefficients_slice(&domain.ifft(&ql_evals));
        let qr_poly =
            DensePolynomial::from_coefficients_slice(&domain.ifft(&qr_evals));
        let qo_poly =
            DensePolynomial::from_coefficients_slice(&domain.ifft(&qo_evals));
        let qpi_poly =
            DensePolynomial::from_coefficients_slice(&domain.ifft(&qpi_evals));

        for (_i, elem) in domain.elements().enumerate() {
            let a = a_poly.evaluate(&elem);
            let b = b_poly.evaluate(&elem);
            let c = c_poly.evaluate(&elem);

            let pi = pi_poly.evaluate(&elem);

            let qm = qm_poly.evaluate(&elem);
            let ql = ql_poly.evaluate(&elem);
            let qr = qr_poly.evaluate(&elem);
            let qo = qo_poly.evaluate(&elem);
            let qpi = qpi_poly.evaluate(&elem);

            let plonk_arith = a * b * qm + a * ql + b * qr + c * qo + pi + qpi;
            assert_eq!(plonk_arith, F::zero());
        }

        let a = WitnessProverOracle {
            label: "a".to_string(),
            poly: a_poly,
            evals_at_coset_of_extended_domain: None,
            queried_rotations: BTreeSet::new(),
            should_permute: false,
            evals: a_evals.clone(),
        };

        let b = WitnessProverOracle {
            label: "b".to_string(),
            poly: b_poly,
            evals_at_coset_of_extended_domain: None,
            queried_rotations: BTreeSet::new(),
            should_permute: false,
            evals: b_evals.clone(),
        };

        let c = WitnessProverOracle {
            label: "c".to_string(),
            poly: c_poly,
            evals_at_coset_of_extended_domain: None,
            queried_rotations: BTreeSet::new(),
            should_permute: false,
            evals: c_evals.clone(),
        };

        let pi = InstanceProverOracle {
            label: "pi".to_string(),
            poly: pi_poly.clone(),
            evals_at_coset_of_extended_domain: None,
            queried_rotations: BTreeSet::new(),
            evals: pi_evals.clone(),
        };

        let mut witness_oracles = [a, b, c];
        let mut instance_oracles = [pi];

        let mut selector_oracles: Vec<_> = [
            (qm_poly.clone(), "qm"),
            (ql_poly.clone(), "ql"),
            (qr_poly.clone(), "qr"),
            (qo_poly.clone(), "qo"),
            (qpi_poly.clone(), "qpi"),
        ]
        .into_iter()
        .map(|(poly, label)| FixedProverOracle::<F> {
            label: label.to_string(),
            evals: domain.fft(&poly),
            poly,
            evals_at_coset_of_extended_domain: None,
            queried_rotations: BTreeSet::new(),
        })
        .collect();

        let mut plonk_vo = GenericVO::<F, PC>::init(
            PrecompiledPlonkArith::get_expr_and_queries(),
        );

        plonk_vo.configure(
            &mut witness_oracles,
            &mut instance_oracles,
            &mut selector_oracles,
        );

        let vos: Vec<&dyn VirtualOracle<F>> = vec![&plonk_vo];

        let vk = Indexer::index(
            &verifier_key,
            &vos,
            &witness_oracles,
            &instance_oracles,
            &selector_oracles,
            domain,
            &domain.vanishing_polynomial().into(),
        )
        .unwrap();

        let pk = ProverKey::from_ck_and_vk(&ck, &vk);

        let preprocessed = ProverPreprocessedInput::new(
            &selector_oracles,
            &vec![],
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

        // Verifier

        let mut witness_ver_oracles: Vec<_> = ["a", "b", "c"]
            .into_iter()
            .map(|label| WitnessVerifierOracle {
                label: label.to_string(),
                queried_rotations: BTreeSet::new(),
                should_permute: false,
                evals_at_challenges: BTreeMap::default(),
                commitment: None,
            })
            .collect();

        let pi = InstanceVerifierOracle {
            label: "pi".to_string(),
            poly: pi_poly.clone(),
            evals: pi_evals.clone(),
            queried_rotations: BTreeSet::new(),
        };

        let mut instance_oracles = [pi];

        let labeled_selectors: Vec<LabeledPolynomial<F, DensePolynomial<F>>> =
            [
                (qm_poly.clone(), "qm"),
                (ql_poly.clone(), "ql"),
                (qr_poly.clone(), "qr"),
                (qo_poly.clone(), "qo"),
                (qpi_poly.clone(), "qpi"),
            ]
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

        let (selector_commitments, _) =
            PC::commit(&ck, labeled_selectors.iter(), None).unwrap();

        let mut selector_oracles: Vec<_> = selector_commitments
            .iter()
            .map(|cmt| FixedVerifierOracle::<F, PC> {
                label: cmt.label().clone(),
                queried_rotations: BTreeSet::default(),
                evals_at_challenges: BTreeMap::default(),
                commitment: Some(cmt.commitment().clone()),
            })
            .collect();

        let mut plonk_vo = GenericVO::<F, PC>::init(
            PrecompiledPlonkArith::get_expr_and_queries(),
        );

        plonk_vo.configure(
            &mut witness_ver_oracles,
            &mut instance_oracles,
            &mut selector_oracles,
        );

        let vos: Vec<&dyn VirtualOracle<F>> = vec![&plonk_vo];

        // Repeat but this time provide verifier witness oracles
        let mut vk = Indexer::index(
            &verifier_key,
            &vos,
            &witness_ver_oracles,
            &instance_oracles,
            &selector_oracles,
            domain,
            &domain.vanishing_polynomial().into(),
        )
        .unwrap();

        let verifier_pp = VerifierPreprocessedInput {
            fixed_oracles: selector_oracles.clone(),
            permutation_oracles: vec![],
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
            &vos,
            domain_size,
            &domain.vanishing_polynomial().into(),
            &mut rng,
        )
        .unwrap();

        assert_eq!(res, ());
    }

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
            // copied from zk-garage
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

        let witness_polys: Vec<_> = [a_evals, b_evals, c_evals, d_evals]
            .iter()
            .map(|evals| {
                DensePolynomial::from_coefficients_slice(&domain.ifft(evals))
            })
            .collect();

        let mut and_xor_vo =
            GenericVO::<F, PC>::init(DeltaXorAnd::get_expr_and_queries());

        let mut witness_oracles: Vec<_> = [
            (witness_polys[0].clone(), "a"),
            (witness_polys[1].clone(), "b"),
            (witness_polys[2].clone(), "product"),
            (witness_polys[3].clone(), "logic"),
        ]
        .into_iter()
        .map(|(poly, label)| WitnessProverOracle::<F> {
            label: label.to_string(),
            poly,
            evals_at_coset_of_extended_domain: None,
            queried_rotations: BTreeSet::new(),
            should_permute: false,
            evals: None,
        })
        .collect();

        let mut instance_oracles = vec![];

        let mut fixed_oracles: Vec<_> = [(q_c_poly.clone(), "qc")]
            .into_iter()
            .map(|(poly, label)| FixedOracle::<F, PC> {
                label: label.to_string(),
                poly,
                evals_at_coset_of_extended_domain: None,
                evals: None,
                queried_rotations: BTreeSet::new(),
                evals_at_challenges: BTreeMap::default(),
                commitment: None,
            })
            .collect();

        and_xor_vo.configure(
            &mut witness_oracles,
            &mut instance_oracles,
            &mut fixed_oracles,
        );

        let vos: Vec<&dyn VirtualOracle<F>> = vec![&and_xor_vo];

        let vk = Indexer::index(
            &ck,
            &verifier_key,
            &vos,
            &witness_oracles,
            &instance_oracles,
            &fixed_oracles,
            &[],
            domain,
            &domain.vanishing_polynomial().into(),
            Adversary::Prover,
        )
        .unwrap();

        let pk = ProverKey::from_ck_and_vk(&ck, &vk);

        let proof = PilInstance::prove(
            &pk,
            &mut witness_oracles,
            &mut instance_oracles,
            vos.as_slice(),
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
                should_mask: false,
                evals_at_challenges: BTreeMap::default(),
                commitment: None,
            })
            .collect();

        let mut instance_oracles = vec![];

        let mut fixed_oracles: Vec<_> = [(q_c_poly.clone(), "qc")]
            .into_iter()
            .map(|(poly, label)| FixedOracle::<F, PC> {
                label: label.to_string(),
                poly,
                evals_at_coset_of_extended_domain: None,
                evals: None,
                queried_rotations: BTreeSet::new(),
                evals_at_challenges: BTreeMap::default(),
                commitment: None,
            })
            .collect();

        let mut and_xor_vo =
            GenericVO::<F, PC>::init(DeltaXorAnd::get_expr_and_queries());

        and_xor_vo.configure(
            &mut witness_ver_oracles,
            &mut instance_oracles,
            &mut fixed_oracles,
        );

        let vos: Vec<&dyn VirtualOracle<F>> = vec![&and_xor_vo];

        let mut vk = Indexer::index(
            &ck,
            &verifier_key,
            &vos,
            &witness_ver_oracles,
            &instance_oracles,
            &fixed_oracles,
            &[],
            domain,
            &domain.vanishing_polynomial().into(),
            Adversary::Verifier,
        )
        .unwrap();

        let res = PilInstance::verify(
            &mut vk,
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
