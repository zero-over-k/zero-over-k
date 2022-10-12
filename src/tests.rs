#[cfg(test)]
mod test {

    use std::collections::{BTreeSet, BTreeMap};

    use ark_bls12_381::{Bls12_381, Fr};
    use ark_ff::{One, Zero};
    use ark_poly::Polynomial;
    use ark_poly::{
        univariate::DensePolynomial, EvaluationDomain, GeneralEvaluationDomain,
        UVPolynomial,
    };

    use ark_poly_commit::PCCommitterKey;
    use ark_std::test_rng;
    use rand_chacha::ChaChaRng;

    use crate::oracles::fixed::FixedOracle;
    use crate::oracles::instance::InstanceOracle;
    use crate::oracles::witness::{WitnessProverOracle, WitnessVerifierOracle};
    use crate::oracles::traits::ConcreteOracle;
    use crate::rng::SimpleHashFiatShamirRng;
    use crate::PIL;
    use crate::vo::precompiled_vos::{GenericVO, PrecompiledMul, PrecompiledVO};
    use blake2::Blake2s;

    use crate::vo::VirtualOracle;
    use crate::{
        commitment::KZG10,
    };

    type F = Fr;
    type FS = SimpleHashFiatShamirRng<Blake2s, ChaChaRng>;
    type PC = KZG10<Bls12_381>;

    type PilInstance = PIL<F, PC, FS>;

    #[test]
    fn test_simple_mul() {
        let max_degree = 17;
        let mut rng = test_rng();

        let srs = PilInstance::universal_setup(max_degree, &mut rng).unwrap();

        let (pk, vk) = PilInstance::prepare_keys(&srs).unwrap();

        let domain_size = 16;
        let poly_degree = domain_size - 1;
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
            should_mask: true,
        };

        let b = WitnessProverOracle {
            label: "b".to_string(),
            poly: b_poly,
            evals_at_coset_of_extended_domain: None,
            queried_rotations: BTreeSet::new(),
            should_mask: true,
        };

        let c = InstanceOracle {
            label: "c".to_string(),
            poly: c_poly.clone(),
            evals_at_coset_of_extended_domain: None,
            queried_rotations: BTreeSet::new(),
        };

        let dummy_fixed = FixedOracle::<F, PC> {
            label: "dummy".to_string(),
            poly: DensePolynomial::default(),
            evals_at_coset_of_extended_domain: None,
            queried_rotations: BTreeSet::default(),
            commitment: None,
        };

        let mut mul_vo = GenericVO::<F>::init(PrecompiledMul::get_expr_and_queries());

        let mut witness_oracles = [a, b];
        let mut instance_oracles = [c];
        // let fixed_oracles: Vec<FixedOracle<F, PC>> = [];

        mul_vo.configure(&witness_oracles, &instance_oracles, &[dummy_fixed]);

        // let concrete_oracles = [a, b, c.clone()];

        let vos: Vec<Box<&dyn VirtualOracle<F>>> = vec![Box::new(&mul_vo)];

        let proof = PilInstance::prove(
            &pk,
            &mut witness_oracles,
            &mut instance_oracles, 
            &mut [],
            vos.as_slice(),
            domain_size,
            &domain.vanishing_polynomial().into(),
            &mut rng,
        )
        .unwrap();

        // let a_verifier = CommittedConcreteOracle::new("a".to_string(), true);
        // let b_verifier = CommittedConcreteOracle::new("b".to_string(), true);
        let a_ver = WitnessVerifierOracle {
            label: "a".to_string(),
            queried_rotations: BTreeSet::default(),
            should_mask: true,
            evals_at_challenges: BTreeMap::default(),
            commitment: None,
        };

        let b_ver = WitnessVerifierOracle {
            label: "b".to_string(),
            queried_rotations: BTreeSet::default(),
            should_mask: true,
            evals_at_challenges: BTreeMap::default(),
            commitment: None,
        };

        // Repeat just to make sure some change from prover does not affect this
        let c = InstanceOracle {
            label: "c".to_string(),
            poly: c_poly,
            evals_at_coset_of_extended_domain: None,
            queried_rotations: BTreeSet::new(),
        };

        let mut ver_wtns_oracles = [a_ver, b_ver];

        let res = PilInstance::verify(
            &vk,
            proof,
            &mut ver_wtns_oracles,
            &mut [c],
            &mut [],
            vos.as_slice(),
            domain_size,
            &domain.vanishing_polynomial().into(),
            &mut rng,
        )
        .unwrap();

        assert_eq!(res, ());
    }

    // #[test]
    // fn test_arith_add() {
    //     let max_degree = 17;
    //     let mut rng = test_rng();

    //     let srs = PilInstance::universal_setup(max_degree, &mut rng).unwrap();

    //     let (pk, vk) = PilInstance::prepare_keys(&srs).unwrap();

    //     let domain_size = 16;
    //     let poly_degree = domain_size - 1;
    //     let domain = GeneralEvaluationDomain::<F>::new(domain_size).unwrap();

    //     let a_poly = DensePolynomial::<F>::rand(poly_degree, &mut rng);
    //     let b_poly = DensePolynomial::<F>::rand(poly_degree, &mut rng);

    //     let a_evals = domain.fft(&a_poly);
    //     let b_evals = domain.fft(&b_poly);

    //     let c_evals = a_evals
    //         .iter()
    //         .zip(b_evals.iter())
    //         .map(|(&a, &b)| a + b)
    //         .collect::<Vec<_>>();

    //     let c_poly =
    //         DensePolynomial::from_coefficients_slice(&domain.ifft(&c_evals));

    //     for elem in domain.elements() {
    //         assert_eq!(
    //             a_poly.evaluate(&elem) + b_poly.evaluate(&elem)
    //                 - c_poly.evaluate(&elem),
    //             F::zero()
    //         );
    //     }

    //     let qm_evals = vec![F::zero(); domain_size];
    //     let ql_evals = vec![F::one(); domain_size];
    //     let qr_evals = vec![F::one(); domain_size];
    //     let qo_evals = vec![-F::one(); domain_size];
    //     let qc_evals = vec![F::zero(); domain_size];

    //     let qm_poly =
    //         DensePolynomial::from_coefficients_slice(&domain.ifft(&qm_evals));
    //     let ql_poly =
    //         DensePolynomial::from_coefficients_slice(&domain.ifft(&ql_evals));
    //     let qr_poly =
    //         DensePolynomial::from_coefficients_slice(&domain.ifft(&qr_evals));
    //     let qo_poly =
    //         DensePolynomial::from_coefficients_slice(&domain.ifft(&qo_evals));
    //     let qc_poly =
    //         DensePolynomial::from_coefficients_slice(&domain.ifft(&qc_evals));

    //     let pi_evals = vec![F::zero(); domain_size];
    //     let pi_poly =
    //         DensePolynomial::from_coefficients_slice(&domain.ifft(&pi_evals));

    //     let mut wires: Vec<InstantiableConcreteOracle<_>> =
    //         [(a_poly, "a"), (b_poly, "b"), (c_poly, "c")]
    //             .into_iter()
    //             .map(|(poly, label)| InstantiableConcreteOracle {
    //                 label: label.to_string(),
    //                 poly,
    //                 evals_at_coset_of_extended_domain: None,
    //                 oracle_type: OracleType::Witness,
    //                 queried_rotations: BTreeSet::new(),
    //                 should_mask: true,
    //             })
    //             .collect();

    //     let mut fixed: Vec<InstantiableConcreteOracle<_>> = [
    //         (qm_poly, "qm"),
    //         (ql_poly, "ql"),
    //         (qr_poly, "qr"),
    //         (qo_poly, "qo"),
    //         (qc_poly, "qc"),
    //     ]
    //     .into_iter()
    //     .map(|(poly, label)| InstantiableConcreteOracle {
    //         label: label.to_string(),
    //         poly,
    //         evals_at_coset_of_extended_domain: None,
    //         oracle_type: OracleType::Witness,
    //         queried_rotations: BTreeSet::new(),
    //         should_mask: false,
    //     })
    //     .collect();

    //     let pi = InstantiableConcreteOracle {
    //         label: "pi".to_string(),
    //         poly: pi_poly,
    //         evals_at_coset_of_extended_domain: None,
    //         oracle_type: OracleType::Instance,
    //         queried_rotations: BTreeSet::new(),
    //         should_mask: false,
    //     };

    //     let mut arith_vo = ArithVO::<F>::new();
    //     arith_vo.configure(&[0, 1, 2, 3, 4, 5, 6, 7], &[0]);

    //     let mut columns = Vec::with_capacity(9);
    //     columns.append(&mut fixed);
    //     columns.append(&mut wires);
    //     columns.push(pi.clone());
    //     let concrete_oracles = columns.as_slice();

    //     let vos: Vec<Box<dyn VirtualOracle<F>>> = vec![Box::new(arith_vo)];

    //     let proof = PilInstance::prove(
    //         &pk,
    //         &concrete_oracles,
    //         &vos,
    //         domain_size,
    //         &domain.vanishing_polynomial().into(),
    //         &mut rng,
    //     )
    //     .unwrap();

    //     let mut witness_oracles: Vec<CommittedConcreteOracle<_, _>> =
    //         ["qm", "ql", "qr", "qo", "qc", "a", "b", "c"]
    //             .iter()
    //             .map(|label| {
    //                 CommittedConcreteOracle::new(label.to_string(), true)
    //             })
    //             .collect();

    //     let _ = PilInstance::verify(
    //         &vk,
    //         proof,
    //         &mut witness_oracles.as_mut_slice(),
    //         &mut [pi],
    //         &vos,
    //         domain_size,
    //         &domain.vanishing_polynomial().into(),
    //         pk.committer_key.max_degree(),
    //         &mut rng,
    //     )
    //     .unwrap();
    // }
}
