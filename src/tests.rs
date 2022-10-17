#[cfg(test)]
mod test {

    use std::collections::{BTreeMap, BTreeSet};

    use ark_bls12_381::{Bls12_381, Fr};
    use ark_ff::{FftField, Field, One, PrimeField, UniformRand, Zero};
    use ark_poly::Polynomial;
    use ark_poly::{
        univariate::DensePolynomial, EvaluationDomain, GeneralEvaluationDomain,
        UVPolynomial,
    };

    use ark_std::test_rng;
    use rand_chacha::ChaChaRng;

    use crate::data_structures::ProverKey;
    use crate::multiproof::poly;
    use crate::oracles::fixed::{self, FixedOracle};
    use crate::oracles::instance::InstanceOracle;

    use crate::oracles::query;
    use crate::oracles::traits::Instantiable;
    use crate::oracles::witness::{WitnessProverOracle, WitnessVerifierOracle};
    use crate::rng::SimpleHashFiatShamirRng;
    use crate::vo::generic_vo::GenericVO;
    use crate::vo::precompiled_vos::{
        PrecompiledMul, PrecompiledPlonkArith, PrecompiledRescue, PrecompiledVO,
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
            evals: None,
        };

        let b = WitnessProverOracle {
            label: "b".to_string(),
            poly: b_poly,
            evals_at_coset_of_extended_domain: None,
            queried_rotations: BTreeSet::new(),
            should_permute: false,
            evals: None,
        };

        let c = InstanceOracle {
            label: "c".to_string(),
            poly: c_poly.clone(),
            evals_at_coset_of_extended_domain: None,
            queried_rotations: BTreeSet::new(),
        };

        let mut mul_vo =
            GenericVO::<F, PC>::init(PrecompiledMul::get_expr_and_queries());

        let mut witness_oracles = [a, b];
        let mut instance_oracles = [c];
        // let fixed_oracles: Vec<FixedOracle<F, PC>> = [];

        mul_vo.configure(&witness_oracles, &instance_oracles, &[]);

        let vos: Vec<&dyn VirtualOracle<F>> = vec![&mul_vo];

        let vk = PilInstance::index(
            &ck,
            &verifier_key,
            &vos,
            &mut witness_oracles,
            &mut instance_oracles,
            &mut [],
            domain,
            domain.vanishing_polynomial().into(),
        )
        .unwrap();

        let pk = ProverKey::from_ck_and_vk(&ck, &vk);

        let proof = PilInstance::prove(
            &pk,
            &mut witness_oracles,
            &mut instance_oracles,
            &vos,
            domain_size,
            &domain.vanishing_polynomial().into(),
            &mut rng,
        )
        .unwrap();

        let a_ver = WitnessVerifierOracle {
            label: "a".to_string(),
            queried_rotations: BTreeSet::default(),
            should_mask: false,
            evals_at_challenges: BTreeMap::default(),
            commitment: None,
        };

        let b_ver = WitnessVerifierOracle {
            label: "b".to_string(),
            queried_rotations: BTreeSet::default(),
            should_mask: false,
            evals_at_challenges: BTreeMap::default(),
            commitment: None,
        };

        // Repeat just to make sure some change from prover does not affect this
        let c = InstanceOracle {
            label: "c".to_string(),
            poly: c_poly.clone(),
            evals_at_coset_of_extended_domain: None,
            queried_rotations: BTreeSet::new(),
        };

        let mut ver_wtns_oracles = [a_ver, b_ver];
        let mut instance_oracles = [c];

        // Repeat but this time provide verifier witness oracles
        let mut vk = PilInstance::index(
            &ck,
            &verifier_key,
            &vos,
            &mut ver_wtns_oracles,
            &mut instance_oracles,
            &mut [],
            domain,
            domain.vanishing_polynomial().into(),
        )
        .unwrap();

        let res = PilInstance::verify(
            &mut vk,
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
        let max_degree = 17;
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

        let fixed_polys: Vec<_> = (0..=3)
            .map(|_| DensePolynomial::<F>::rand(poly_degree, &mut rng))
            .collect();
        let fixed_evals: Vec<Vec<F>> =
            fixed_polys.iter().map(|poly| domain.fft(&poly)).collect();

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
        .map(|(w1, w2, w3, w4, w5, &q1, &q2, &q3, &q4)| {
            q1 * pow_5(w1) + q2 * pow_5(w2) + q3 * pow_5(w3) + q4 * pow_5(w4)
            // - pow_5(w5) //TODO: should this value be here
        })
        .collect();

        let w5_poly =
            DensePolynomial::from_coefficients_slice(&domain.ifft(&w5_evals));

        let mut rescue_vo =
            GenericVO::<F, PC>::init(PrecompiledRescue::get_expr_and_queries());

        let mut witness_oracles: Vec<_> = [
            (witness_polys[0].clone(), "a"),
            (witness_polys[1].clone(), "b"),
            (witness_polys[2].clone(), "c"),
            (witness_polys[3].clone(), "d"),
            (w5_poly, "e"),
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

        let mut fixed_oracles: Vec<_> = [
            (fixed_polys[0].clone(), "q1"),
            (fixed_polys[1].clone(), "q2"),
            (fixed_polys[2].clone(), "q3"),
            (fixed_polys[3].clone(), "q4"),
        ]
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

        rescue_vo.configure(
            &witness_oracles,
            &instance_oracles,
            &fixed_oracles,
        );

        // q_expr[0].clone() * pow_5(&w_expr[0])
        // + q_expr[1].clone() * pow_5(&w_expr[1])
        // + q_expr[2].clone() * pow_5(&w_expr[2])
        // + q_expr[3].clone() * pow_5(&w_expr[3])
        // - w_expr[4].clone()
        for elem in domain.elements() {
            let q1 = fixed_oracles[0].polynomial().evaluate(&elem);
            let q2 = fixed_oracles[1].polynomial().evaluate(&elem);
            let q3 = fixed_oracles[2].polynomial().evaluate(&elem);
            let q4 = fixed_oracles[3].polynomial().evaluate(&elem);

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

        let vk = PilInstance::index(
            &ck,
            &verifier_key,
            &vos,
            &mut witness_oracles,
            &mut instance_oracles,
            &mut fixed_oracles,
            domain,
            domain.vanishing_polynomial().into(),
        )
        .unwrap();

        let pk = ProverKey::from_ck_and_vk(&ck, &vk);

        let proof = PilInstance::prove(
            &pk,
            &mut witness_oracles,
            &mut instance_oracles,
            &vos,
            domain_size,
            &domain.vanishing_polynomial().into(),
            &mut rng,
        )
        .unwrap();

        let mut witness_ver_oracles: Vec<_> = ["a", "b", "c", "d", "e"]
            .into_iter()
            .map(|label| WitnessVerifierOracle {
                label: label.to_string(),
                queried_rotations: BTreeSet::new(),
                should_mask: false,
                evals_at_challenges: BTreeMap::default(),
                commitment: None,
            })
            .collect();

        // Repeat but this time provide verifier witness oracles
        let mut vk = PilInstance::index(
            &ck,
            &verifier_key,
            &vos,
            &mut witness_ver_oracles,
            &mut instance_oracles,
            &mut fixed_oracles,
            domain,
            domain.vanishing_polynomial().into(),
        )
        .unwrap();

        let res = PilInstance::verify(
            &mut vk,
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

        for (i, elem) in domain.elements().enumerate() {
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
            evals: None,
        };

        let b = WitnessProverOracle {
            label: "b".to_string(),
            poly: b_poly,
            evals_at_coset_of_extended_domain: None,
            queried_rotations: BTreeSet::new(),
            should_permute: false,
            evals: None,
        };

        let c = WitnessProverOracle {
            label: "c".to_string(),
            poly: c_poly,
            evals_at_coset_of_extended_domain: None,
            queried_rotations: BTreeSet::new(),
            should_permute: false,
            evals: None,
        };

        let pi = InstanceOracle {
            label: "pi".to_string(),
            poly: pi_poly.clone(),
            evals_at_coset_of_extended_domain: None,
            queried_rotations: BTreeSet::new(),
        };

        let mut witness_oracles = [a, b, c];
        let mut instance_oracles = [pi];

        let mut fixed_oracles: Vec<_> = [
            (qm_poly.clone(), "qm"),
            (ql_poly.clone(), "ql"),
            (qr_poly.clone(), "qr"),
            (qo_poly.clone(), "qo"),
            (qpi_poly.clone(), "qpi"),
        ]
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

        let mut plonk_vo =
            GenericVO::<F, PC>::init(PrecompiledPlonkArith::get_expr_and_queries());
        plonk_vo.configure(&witness_oracles, &instance_oracles, &fixed_oracles);

        let vos: Vec<&dyn VirtualOracle<F>> = vec![&plonk_vo];

        let vk = PilInstance::index(
            &ck,
            &verifier_key,
            &vos,
            &mut witness_oracles,
            &mut instance_oracles,
            &mut fixed_oracles,
            domain,
            domain.vanishing_polynomial().into(),
        )
        .unwrap();

        let pk = ProverKey::from_ck_and_vk(&ck, &vk);

        let proof = PilInstance::prove(
            &pk,
            &mut witness_oracles,
            &mut instance_oracles,
            &vos,
            domain_size,
            &domain.vanishing_polynomial().into(),
            &mut rng,
        )
        .unwrap();

        let mut witness_ver_oracles: Vec<_> = ["a", "b", "c"]
            .into_iter()
            .map(|label| WitnessVerifierOracle {
                label: label.to_string(),
                queried_rotations: BTreeSet::new(),
                should_mask: false,
                evals_at_challenges: BTreeMap::default(),
                commitment: None,
            })
            .collect();

        // repeat pi
        let pi = InstanceOracle {
            label: "pi".to_string(),
            poly: pi_poly.clone(),
            evals_at_coset_of_extended_domain: None,
            queried_rotations: BTreeSet::new(),
        };

        let mut instance_oracles = [pi];

        // Repeat but this time provide verifier witness oracles
        let mut vk = PilInstance::index(
            &ck,
            &verifier_key,
            &vos,
            &mut witness_ver_oracles,
            &mut instance_oracles,
            &mut fixed_oracles,
            domain,
            domain.vanishing_polynomial().into(),
        )
        .unwrap();

        let res = PilInstance::verify(
            &mut vk,
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
}
