use super::{query::VirtualQuery, virtual_expression::VirtualExpression};
use crate::oracles::{query::OracleType, rotation::Rotation};
use ark_ff::PrimeField;

pub trait PrecompiledVO<F: PrimeField> {
    fn get_expr_and_queries() -> (VirtualExpression<F>, Vec<VirtualQuery>);
}

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

/// Rescue VO implements a 4 element vector multiplication and a exponentiation:
/// (q1, q2, q3, q4) * (w1, w2, w3, w4)^5  = w5
/// Constraint :
/// q_1 * w_1^5 +
/// q_2 * w_2^5 +
/// q_3 * w_3^5 +
/// q_4 * w_4^5 -
/// w_5 = 0
pub struct PrecompiledRescue {}

impl<F> PrecompiledVO<F> for PrecompiledRescue
where
    F: PrimeField,
{
    fn get_expr_and_queries() -> (VirtualExpression<F>, Vec<VirtualQuery>) {
        let q = (0..=3).map(|index| {
            VirtualQuery::new(index, Rotation::curr(), OracleType::Fixed)
        });
        let w = (0..=4).map(|index| {
            VirtualQuery::new(index, Rotation::curr(), OracleType::Witness)
        });
        let oracles = q.clone().chain(w.clone()).collect();

        let rescue_expr = {
            let q_expr: Vec<VirtualExpression<F>> =
                q.map(|query| query.into()).collect();
            let w_expr: Vec<VirtualExpression<F>> =
                w.map(|query| query.into()).collect();
            let pow_5 = |e: &VirtualExpression<F>| {
                e.clone() * e.clone() * e.clone() * e.clone() * e.clone()
            };

            q_expr[0].clone() * pow_5(&w_expr[0])
                + q_expr[1].clone() * pow_5(&w_expr[1])
                + q_expr[2].clone() * pow_5(&w_expr[2])
                + q_expr[3].clone() * pow_5(&w_expr[3])
                - w_expr[4].clone()
        };

        (rescue_expr, oracles)
    }
}

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
            let d: VirtualExpression<F> = d.clone().into();

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
        let expr = {
            let a: VirtualExpression<F> = a.clone().into();
            let a_next: VirtualExpression<F> = a_next.clone().into();
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
            delta(a_next - const_4 * a)
        };

        (expr, vec![a])
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
    use std::collections::{BTreeMap, BTreeSet};

    use crate::{
        oracles::{
            fixed::FixedProverOracle, instance::InstanceProverOracle,
            witness::WitnessProverOracle,
        },
        vo::generic_vo::GenericVO,
    };

    use super::{PrecompiledMul, PrecompiledRescue, PrecompiledVO};
    use crate::commitment::KZG10;
    use ark_bls12_381::{Bls12_381, Fr as F};
    use ark_ff::Zero;
    use ark_poly::univariate::DensePolynomial;

    type PC = KZG10<Bls12_381>;

    #[test]
    fn test_simple_mul() {
        let mut mul_vo =
            GenericVO::<F, PC>::init(PrecompiledMul::get_expr_and_queries());

        let a = WitnessProverOracle::<F> {
            label: "a".to_string(),
            poly: DensePolynomial::default(),
            evals_at_coset_of_extended_domain: None,
            queried_rotations: BTreeSet::new(),
            should_permute: false,
            evals: vec![F::zero(); 1],
        };

        let b = WitnessProverOracle::<F> {
            label: "b".to_string(),
            poly: DensePolynomial::default(),
            evals_at_coset_of_extended_domain: None,
            queried_rotations: BTreeSet::new(),
            should_permute: false,
            evals: vec![F::zero(); 1],
        };

        let c = InstanceProverOracle::<F> {
            label: "c".to_string(),
            poly: DensePolynomial::default(),
            evals_at_coset_of_extended_domain: None,
            queried_rotations: BTreeSet::new(),
            evals: vec![F::zero(); 1],
        };

        let mut witness_oracles = vec![a, b];
        let mut instance_oracles = vec![c];
        let mut fixed_oracles: Vec<FixedProverOracle<F>> = vec![];

        mul_vo.configure(
            &mut witness_oracles,
            &mut instance_oracles,
            &mut fixed_oracles,
        );
    }

    #[test]
    fn test_rescue_gate() {
        let mut rescue_vo =
            GenericVO::<F, PC>::init(PrecompiledRescue::get_expr_and_queries());

        let mut witness_oracles: Vec<_> = ["a", "b", "c", "d", "e"]
            .into_iter()
            .map(|label| WitnessProverOracle::<F> {
                label: label.to_string(),
                poly: DensePolynomial::default(),
                evals_at_coset_of_extended_domain: None,
                queried_rotations: BTreeSet::new(),
                should_permute: false,
                evals: vec![F::zero(); 0],
            })
            .collect();

        let mut instance_oracles: Vec<InstanceProverOracle<F>> = vec![];

        let mut fixed_oracles: Vec<_> = ["q1", "q2", "q3", "q4"]
            .into_iter()
            .map(|label| FixedProverOracle::<F> {
                label: label.to_string(),
                poly: DensePolynomial::default(),
                evals_at_coset_of_extended_domain: None,
                evals: vec![F::zero(); 0],
                queried_rotations: BTreeSet::default(),
            })
            .collect();

        rescue_vo.configure(
            &mut witness_oracles,
            &mut instance_oracles,
            &mut fixed_oracles,
        );
    }
}
