#[cfg(test)]
mod test {

    use std::collections::BTreeSet;

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

    use crate::concrete_oracle::CommittedConcreteOracle;
    use crate::rng::SimpleHashFiatShamirRng;
    use crate::vo::precompiled::arith::ArithVO;
    use crate::PIL;
    use blake2::Blake2s;

    use crate::vo::VirtualOracle;
    use crate::{
        commitment::KZG10,
        concrete_oracle::{InstantiableConcreteOracle, OracleType},
        vo::precompiled::mul::MulVO,
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

        let a = InstantiableConcreteOracle {
            label: "a".to_string(),
            poly: a_poly,
            evals_at_coset_of_extended_domain: None,
            oracle_type: OracleType::Witness,
            queried_rotations: BTreeSet::new(),
            should_mask: true,
        };

        let b = InstantiableConcreteOracle {
            label: "b".to_string(),
            poly: b_poly,
            evals_at_coset_of_extended_domain: None,
            oracle_type: OracleType::Witness,
            queried_rotations: BTreeSet::new(),
            should_mask: true,
        };

        let c = InstantiableConcreteOracle {
            label: "c".to_string(),
            poly: c_poly,
            evals_at_coset_of_extended_domain: None,
            oracle_type: OracleType::Instance,
            queried_rotations: BTreeSet::new(),
            should_mask: false,
        };

        let mut mul_vo = MulVO::<F>::new();
        mul_vo.configure(&[0, 1], &[0]);

        let concrete_oracles = [a, b, c.clone()];

        let vos: Vec<Box<dyn VirtualOracle<F>>> = vec![Box::new(mul_vo)];

        let proof = PilInstance::prove(
            &pk,
            &concrete_oracles,
            &vos,
            domain_size,
            &domain.vanishing_polynomial().into(),
            &mut rng,
        )
        .unwrap();

        let a_verifier = CommittedConcreteOracle::new("a".to_string(), true);
        let b_verifier = CommittedConcreteOracle::new("b".to_string(), true);

        let res = PilInstance::verify(
            &vk,
            proof,
            &mut [a_verifier, b_verifier],
            &mut [c],
            &vos,
            domain_size,
            &domain.vanishing_polynomial().into(),
            pk.committer_key.max_degree(),
            &mut rng,
        )
        .unwrap();

        assert_eq!(res, ());
    }

    #[test]
    fn test_arith_add() {
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
            .map(|(&a, &b)| a + b)
            .collect::<Vec<_>>();

        let c_poly =
            DensePolynomial::from_coefficients_slice(&domain.ifft(&c_evals));

        for elem in domain.elements() {
            assert_eq!(
                a_poly.evaluate(&elem) + b_poly.evaluate(&elem)
                    - c_poly.evaluate(&elem),
                F::zero()
            );
        }

        let qm_evals = vec![F::zero(); domain_size];
        let ql_evals = vec![F::one(); domain_size];
        let qr_evals = vec![F::one(); domain_size];
        let qo_evals = vec![-F::one(); domain_size];
        let qc_evals = vec![F::zero(); domain_size];

        let qm_poly =
            DensePolynomial::from_coefficients_slice(&domain.ifft(&qm_evals));
        let ql_poly =
            DensePolynomial::from_coefficients_slice(&domain.ifft(&ql_evals));
        let qr_poly =
            DensePolynomial::from_coefficients_slice(&domain.ifft(&qr_evals));
        let qo_poly =
            DensePolynomial::from_coefficients_slice(&domain.ifft(&qo_evals));
        let qc_poly =
            DensePolynomial::from_coefficients_slice(&domain.ifft(&qc_evals));

        let pi_evals = vec![F::zero(); domain_size];
        let pi_poly =
            DensePolynomial::from_coefficients_slice(&domain.ifft(&pi_evals));

        let mut wires: Vec<InstantiableConcreteOracle<_>> =
            [(a_poly, "a"), (b_poly, "b"), (c_poly, "c")]
                .into_iter()
                .map(|(poly, label)| InstantiableConcreteOracle {
                    label: label.to_string(),
                    poly,
                    evals_at_coset_of_extended_domain: None,
                    oracle_type: OracleType::Witness,
                    queried_rotations: BTreeSet::new(),
                    should_mask: true,
                })
                .collect();

        let mut fixed: Vec<InstantiableConcreteOracle<_>> = [
            (qm_poly, "qm"),
            (ql_poly, "ql"),
            (qr_poly, "qr"),
            (qo_poly, "qo"),
            (qc_poly, "qc"),
        ]
        .into_iter()
        .map(|(poly, label)| InstantiableConcreteOracle {
            label: label.to_string(),
            poly,
            evals_at_coset_of_extended_domain: None,
            oracle_type: OracleType::Witness,
            queried_rotations: BTreeSet::new(),
            should_mask: false,
        })
        .collect();

        let pi = InstantiableConcreteOracle {
            label: "pi".to_string(),
            poly: pi_poly,
            evals_at_coset_of_extended_domain: None,
            oracle_type: OracleType::Instance,
            queried_rotations: BTreeSet::new(),
            should_mask: false,
        };

        let mut arith_vo = ArithVO::<F>::new();
        arith_vo.configure(&[0, 1, 2, 3, 4, 5, 6, 7], &[0]);

        wires.append(&mut fixed);
        wires.push(pi.clone());
        let concrete_oracles = wires.as_slice();

        let vos: Vec<Box<dyn VirtualOracle<F>>> = vec![Box::new(arith_vo)];

        let proof = PilInstance::prove(
            &pk,
            &concrete_oracles,
            &vos,
            domain_size,
            &domain.vanishing_polynomial().into(),
            &mut rng,
        )
        .unwrap();

        let mut witness_oracles: Vec<CommittedConcreteOracle<_, _>> =
            ["qm", "ql", "qr", "qo", "qc", "a", "b", "c"]
                .iter()
                .map(|label| {
                    CommittedConcreteOracle::new(label.to_string(), true)
                })
                .collect();

        let _ = PilInstance::verify(
            &vk,
            proof,
            &mut witness_oracles.as_mut_slice(),
            &mut [pi],
            &vos,
            domain_size,
            &domain.vanishing_polynomial().into(),
            pk.committer_key.max_degree(),
            &mut rng,
        )
        .unwrap();
    }
}
