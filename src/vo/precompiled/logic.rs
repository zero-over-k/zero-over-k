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
        let d = VirtualQuery::new(3, Rotation::curr(), OracleType::Witness);
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

    use std::iter::successors;

    use ark_bls12_381::Fr;
    use ark_ff::{One, Zero};

    use ark_poly::EvaluationDomain;

    use ark_std::rand::RngCore;

    use crate::vo::generic_vo::GenericVO;
    use crate::vo::precompiled::tests::{
        run_prover,
        run_verifier,
        test_init,
    };

    use itertools::izip;

    type F = Fr;

    #[test]
    fn test_delta() {
        // Initialize context
        let (domain, cs_keys, mut rng) = test_init(16usize);

        // Generate circuit evals
        let domain_size = domain.size();

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

        let mut q_last_evals = vec![F::zero(); domain_size];
        q_last_evals[domain_size - 1] = F::one();

        // check
        let delta =
            |v| v * (v - F::one()) * (v - F::from(2u32)) * (v - F::from(3u32));
        for (i, &v) in a_evals.iter().enumerate() {
            if i < domain_size - 1 {
                assert_eq!(F::zero(), delta(a_evals[i + 1] - F::from(4u32) * v))
            }
        }

        let fixed = vec![("q_last", q_last_evals.as_slice())];
        let instance: Vec<(&str, &[F])> = vec![];

        // Run prover
        let delta_vo = GenericVO::<F>::init(Delta::get_expr_and_queries());
        let proof = run_prover(
            domain,
            cs_keys.0.clone(),
            cs_keys.1.clone(),
            vec![("a", &a_evals)],
            fixed.clone(),
            instance.clone(),
            delta_vo.clone(),
            &mut rng,
        );

        // Run verifier
        let res = run_verifier(
            domain,
            cs_keys.0,
            cs_keys.1,
            vec!["a"],
            fixed,
            instance,
            delta_vo,
            proof,
            &mut rng,
        );

        assert_eq!(res, ());
    }

    // TODO Fix test
    #[test]
    fn test_delta_xor_and() {
        // Initialize context
        let (domain, cs_keys, mut rng) = test_init(32usize);

        // Generate circuit evals

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

        let witness = vec![
            ("a", a_evals.as_slice()),
            ("b", b_evals.as_slice()),
            ("product", c_evals.as_slice()),
            ("logic", d_evals.as_slice()),
        ];

        let fixed = vec![("qc", q_c_evals)];
        let instance: Vec<(&str, &[F])> = vec![];

        // Run prover
        let xor_and_vo =
            GenericVO::<F>::init(DeltaXorAnd::get_expr_and_queries());
        let proof = run_prover(
            domain,
            cs_keys.0.clone(),
            cs_keys.1.clone(),
            witness,
            fixed.clone(),
            instance.clone(),
            xor_and_vo.clone(),
            &mut rng,
        );

        // Run verifier
        let res = run_verifier(
            domain,
            cs_keys.0,
            cs_keys.1,
            vec!["a", "b", "product", "logic"],
            fixed,
            instance,
            xor_and_vo,
            proof,
            &mut rng,
        );

        assert_eq!(res, ());
    }
}
