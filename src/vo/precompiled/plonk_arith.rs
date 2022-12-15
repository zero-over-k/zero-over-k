use crate::{
    oracles::{query::OracleType, rotation::Rotation},
    vo::{query::VirtualQuery, virtual_expression::VirtualExpression},
};
use ark_ff::PrimeField;

use super::PrecompiledVO;

/// Plonk's original arithmetic constraint:
/// q_m * a * b + q_L * a + q_R * b + q_o * c + q_c + PI = 0
pub struct PrecompiledPlonkArith {}

impl<F: PrimeField> PrecompiledVO<F> for PrecompiledPlonkArith {
    fn get_expr_and_queries() -> (VirtualExpression<F>, Vec<VirtualQuery>) {
        // Selectors
        let qm = VirtualQuery::new(0, Rotation::curr(), OracleType::Fixed);
        let ql = VirtualQuery::new(1, Rotation::curr(), OracleType::Fixed);
        let qr = VirtualQuery::new(2, Rotation::curr(), OracleType::Fixed);
        let qo = VirtualQuery::new(3, Rotation::curr(), OracleType::Fixed);
        let qc = VirtualQuery::new(4, Rotation::curr(), OracleType::Fixed);

        // Pub input
        let pi = VirtualQuery::new(0, Rotation::curr(), OracleType::Instance);

        // Witnesses
        let a = VirtualQuery::new(0, Rotation::curr(), OracleType::Witness);
        let b = VirtualQuery::new(1, Rotation::curr(), OracleType::Witness);
        let c = VirtualQuery::new(2, Rotation::curr(), OracleType::Witness);

        let plonk_expression = {
            let qm: VirtualExpression<F> = qm.clone().into();
            let ql: VirtualExpression<F> = ql.clone().into();
            let qr: VirtualExpression<F> = qr.clone().into();
            let qo: VirtualExpression<F> = qo.clone().into();
            let qc: VirtualExpression<F> = qc.clone().into();

            let pi: VirtualExpression<F> = pi.clone().into();

            let a: VirtualExpression<F> = a.clone().into();
            let b: VirtualExpression<F> = b.clone().into();
            let c: VirtualExpression<F> = c.clone().into();

            a.clone() * b.clone() * qm + a * ql + b * qr + c * qo + qc + pi
        };

        (plonk_expression, vec![qm, ql, qr, qo, qc, pi, a, b, c])
    }
}

/// Plonk's orginal arithmetic constraint with an extra addend using 4 wires.
/// q_m * a * b + q_L * a + q_R * b + q_o * c + q_4 * d + q_c + PI = 0
pub struct PlonkArith4 {}

impl<F: PrimeField> PrecompiledVO<F> for PlonkArith4 {
    fn get_expr_and_queries() -> (VirtualExpression<F>, Vec<VirtualQuery>) {
        // Selectors
        let qm = VirtualQuery::new(0, Rotation::curr(), OracleType::Fixed);
        let ql = VirtualQuery::new(1, Rotation::curr(), OracleType::Fixed);
        let qr = VirtualQuery::new(2, Rotation::curr(), OracleType::Fixed);
        let q4 = VirtualQuery::new(3, Rotation::curr(), OracleType::Fixed);
        let qo = VirtualQuery::new(4, Rotation::curr(), OracleType::Fixed);
        let qc = VirtualQuery::new(5, Rotation::curr(), OracleType::Fixed);

        // Pub input
        let pi = VirtualQuery::new(0, Rotation::curr(), OracleType::Instance);

        // Witnesses
        let a = VirtualQuery::new(0, Rotation::curr(), OracleType::Witness);
        let b = VirtualQuery::new(1, Rotation::curr(), OracleType::Witness);
        let c = VirtualQuery::new(2, Rotation::curr(), OracleType::Witness);
        let d = VirtualQuery::new(2, Rotation::curr(), OracleType::Witness);

        let plonk_expression = {
            let qm: VirtualExpression<F> = qm.clone().into();
            let ql: VirtualExpression<F> = ql.clone().into();
            let qr: VirtualExpression<F> = qr.clone().into();
            let q4: VirtualExpression<F> = q4.clone().into();
            let qo: VirtualExpression<F> = qo.clone().into();
            let qc: VirtualExpression<F> = qc.clone().into();

            let pi: VirtualExpression<F> = pi.clone().into();

            let a: VirtualExpression<F> = a.clone().into();
            let b: VirtualExpression<F> = b.clone().into();
            let c: VirtualExpression<F> = c.clone().into();
            let d: VirtualExpression<F> = d.into();

            a.clone() * b.clone() * qm
                + a * ql
                + b * qr
                + d * q4
                + c * qo
                + pi
                + qc
        };

        (plonk_expression, vec![qm, ql, qr, q4, qo, qc, pi, a, b, c])
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use ark_bls12_381::Fr;
    use ark_ff::{One, UniformRand, Zero};
    use ark_poly::{
        univariate::DensePolynomial, EvaluationDomain, UVPolynomial,
    };

    use crate::vo::generic_vo::GenericVO;
    use crate::vo::precompiled::tests::{run_prover, run_verifier, test_init};

    type F = Fr;

    #[test]
    fn test_plonk_arith() {
        // Initialize context
        let (domain, cs_keys, mut rng) = test_init(4usize);

        // Generate circuit evals
        let domain_size = domain.size();
        let poly_degree = domain_size - 1;
        // let mut rng = test_rng();

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

        // check
        for (i, _) in domain.elements().enumerate() {
            let a = a_evals[i];
            let b = b_evals[i];
            let c = c_evals[i];

            let pi = pi_evals[i];

            let qm = qm_evals[i];
            let ql = ql_evals[i];
            let qr = qr_evals[i];
            let qo = qo_evals[i];
            let qpi = qpi_evals[i];

            let plonk_arith = a * b * qm + a * ql + b * qr + c * qo + pi + qpi;
            assert_eq!(plonk_arith, F::zero());
        }

        let fixed: Vec<(_, &[F])> = vec![
            ("qm", &qm_evals),
            ("ql", &ql_evals),
            ("qr", &qr_evals),
            ("qo", &qo_evals),
            ("qpi", &qpi_evals),
        ];
        let instance: Vec<(_, &[F])> = vec![("pi", &pi_evals)];

        // Run prover
        let plonk_vo =
            GenericVO::<F>::init(PrecompiledPlonkArith::get_expr_and_queries());
        let proof = run_prover(
            domain,
            cs_keys.0.clone(),
            cs_keys.1.clone(),
            vec![("a", &a_evals), ("b", &b_evals), ("c", &c_evals)],
            fixed.clone(),
            instance.clone(),
            plonk_vo.clone(),
            &mut rng,
        );

        // Run verifier
        let res = run_verifier(
            domain,
            cs_keys.0,
            cs_keys.1,
            vec!["a", "b", "c"],
            fixed,
            instance,
            plonk_vo,
            proof,
        );

        assert!(res.is_ok());
    }
}
