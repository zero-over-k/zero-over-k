use super::PrecompiledVO;
use crate::{
    oracles::{query::OracleType, rotation::Rotation},
    vo::{query::VirtualQuery, virtual_expression::VirtualExpression},
};
use ark_ff::PrimeField;

pub struct PrecompiledMul {}

impl<F: PrimeField> PrecompiledVO<F> for PrecompiledMul {
    fn get_expr_and_queries() -> (VirtualExpression<F>, Vec<VirtualQuery>) {
        let q1 = VirtualQuery::new(0, Rotation::curr(), OracleType::Witness);
        let q2 = VirtualQuery::new(1, Rotation::curr(), OracleType::Witness);
        let q3 = VirtualQuery::new(0, Rotation::curr(), OracleType::Instance);

        let mul_expression = {
            let a: VirtualExpression<F> = q1.clone().into();
            let b: VirtualExpression<F> = q2.clone().into();
            let c: VirtualExpression<F> = q3.clone().into();

            a * b - c
        };

        (mul_expression, vec![q1, q2, q3])
    }
}

#[cfg(test)]
mod test {
    use super::PrecompiledMul;
    use crate::vo::precompiled::tests::{run_prover, run_verifier, test_init};
    use ark_bls12_381::Fr;
    use ark_ff::Zero;
    use ark_poly::Polynomial;
    use ark_poly::{
        univariate::DensePolynomial, EvaluationDomain, GeneralEvaluationDomain,
        UVPolynomial,
    };
    use crate::vo::generic_vo::GenericVO;
    use crate::vo::precompiled::PrecompiledVO;

    type F = Fr;

    #[test]
    fn test_simple_mul() {
        // Initialize context
        let domain_size = 16;
        let (_, cs_keys, mut rng) = test_init(domain_size);
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

        let mul_vo =
            GenericVO::<F>::init(PrecompiledMul::get_expr_and_queries());

        let witness_labels = vec!["a", "b"];
        let witness_evals = vec![a_evals, b_evals];
        let witness: Vec<(_, &[F])> = witness_evals
            .iter()
            .zip(witness_labels.clone().into_iter())
            .map(|(evals, label)| (label, evals.as_slice()))
            .collect();

        let instance = vec![
            ("c", c_evals.as_slice()),
        ];
        let fixed: Vec<(String, &[F])> = vec![];

        let proof = run_prover(
            domain,
            cs_keys.0.clone(),
            cs_keys.1.clone(),
            witness.clone(),
            fixed.clone(),
            instance.clone(),
            mul_vo.clone(),
            &mut rng,
        );

        let res = run_verifier(
            domain,
            cs_keys.0,
            cs_keys.1,
            witness_labels,
            fixed,
            instance,
            mul_vo.clone(),
            proof,
            &mut rng,
        );

        assert_eq!(res, ());

        // println!("{}", proof.info());
        // println!("{}", proof.cumulative_info());
    }
}
