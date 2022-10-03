#[cfg(test)]
mod test {
    use ark_bls12_381::{Fr, Bls12_381};
    use ark_ff::{Field, Zero};
    use ark_poly::Polynomial;
    use ark_poly::{univariate::DensePolynomial, UVPolynomial, GeneralEvaluationDomain, EvaluationDomain};
    use ark_poly_commit::marlin_pc::MarlinKZG10;
    use ark_std::test_rng;
    use rand_chacha::ChaChaRng;
    use ark_poly_commit::PCCommitterKey;

    use blake2::Blake2s;
    use crate::PIL;
    use crate::rng::{FiatShamirRng, SimpleHashFiatShamirRng};

    use crate::vo::VirtualOracle;
    use crate::{concrete_oracle::{ProverConcreteOracle, OracleType}, vo::{precompiled::mul::MulVO}};

    type F = Fr;
    type FS = SimpleHashFiatShamirRng<Blake2s, ChaChaRng>;
    type PC = MarlinKZG10<Bls12_381, DensePolynomial<F>>;

    type PilInstance = PIL<F, PC, FS>;

    // TODO: make sure to test quotient splitting

    #[test]
    fn test_simple_mul() {
        let max_degree = 30;
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

        let c_evals = a_evals.iter().zip(b_evals.iter()).map(|(&a, &b)| {
            a * b
        }).collect::<Vec<_>>();

        let c_poly = DensePolynomial::from_coefficients_slice(&domain.ifft(&c_evals));

        for elem in domain.elements() {
            assert_eq!(a_poly.evaluate(&elem) * b_poly.evaluate(&elem) - c_poly.evaluate(&elem), F::zero());
        }

        let a = ProverConcreteOracle {
            label: "a".to_string(),
            poly: a_poly,
            evals_at_coset_of_extended_domain: None,
            oracle_type: OracleType::Witness,
            queried_rotations: vec![],
            should_mask: false,
        };

        let b = ProverConcreteOracle {
            label: "b".to_string(),
            poly: b_poly,
            evals_at_coset_of_extended_domain: None,
            oracle_type: OracleType::Witness,
            queried_rotations: vec![],
            should_mask: false,
        };

        let c = ProverConcreteOracle {
            label: "c".to_string(),
            poly: c_poly,
            evals_at_coset_of_extended_domain: None,
            oracle_type: OracleType::Instance,
            queried_rotations: vec![],
            should_mask: false,
        };

        let mut mul_vo = MulVO::<F>::new();
        mul_vo.configure(&[0, 1], &[0]);

        let concrete_oracles = [a, b, c];

        let vos: Vec<Box<dyn VirtualOracle<F>>> = vec![Box::new(mul_vo)];

        let _ = PilInstance::prove(&pk, &concrete_oracles, &vos, domain_size, &domain.vanishing_polynomial().into(), &mut rng).unwrap();

    }
}