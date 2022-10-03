#[cfg(test)]
mod test {
    use ark_bls12_381::{Fr, Bls12_381};
    use ark_ff::Field;
    use ark_poly::{univariate::DensePolynomial, UVPolynomial, GeneralEvaluationDomain, EvaluationDomain};
    use ark_poly_commit::marlin_pc::MarlinKZG10;
    use ark_std::test_rng;
    use rand_chacha::ChaChaRng;

    use blake2::Blake2s;
    use crate::PIL;
    use crate::rng::{FiatShamirRng, SimpleHashFiatShamirRng};

    use crate::{concrete_oracle::{ProverConcreteOracle, OracleType}, vo::{precompiled::mul::MulVO}};

    type F = Fr;
    type FS = SimpleHashFiatShamirRng<Blake2s, ChaChaRng>;
    type PC = MarlinKZG10<Bls12_381, DensePolynomial<F>>;

    type PilInstance = PIL<F, PC, FS>;


    #[test]
    fn test_simple_mul() {
        let max_degree = 50;
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

        let c_evals = a_evals.iter().zip(b_evals.iter()).map(|(&a, b)| {
            a * b.inverse().unwrap()
        }).collect::<Vec<_>>();


        let c_poly = DensePolynomial::from_coefficients_slice(&domain.ifft(&c_evals));

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

        // let vos = vec![Box::new(mul_vo)];

        // let _ = PilInstance::prove(&pk, &concrete_oracles, &vos, domain_size, &domain.vanishing_polynomial().into(), &mut rng);

    }

    #[test]
    fn try_it() {

        // Use at least two approaches to make it work.
        // DON'T add/remove any code line.
        trait MyTrait {
            fn f(&self) -> usize;
        }

        impl MyTrait for u32 {
            fn f(&self) -> usize {
                42
            }
        }

        impl MyTrait for String {
            fn f(&self) -> usize {
                42
            }
        }

        fn my_function<'a>(vos: &'a Vec<Box<dyn MyTrait>>) {
            for vo in vos {
                vo.f();
            }
        }  

        fn main() {
            // let vos = vec![Box::new(u_32::from(31)), Box::new(String::from("abc"))];
            // my_function(Box::new(13_u32));
            // my_function(Box::new(String::from("abc")));

            // let s = String::from("a");
            // my_function(Box::new(s));

            println!("Success!");
        }

    }
}