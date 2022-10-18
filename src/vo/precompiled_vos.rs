use ark_ff::PrimeField;

use crate::oracles::{query::OracleType, rotation::Rotation};

use super::{query::VirtualQuery, virtual_expression::VirtualExpression};

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

/// Implements 4-width rescue:
/// q_1 * w_1^5 +
/// q_2 * w_2^5 +
/// q_3 * w_3^5 +
/// q_4 * w_4^5 =
/// w_5
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

pub struct PrecompiledPlonkArith {}

impl<F: PrimeField> PrecompiledVO<F> for PrecompiledPlonkArith {
    fn get_expr_and_queries() -> (VirtualExpression<F>, Vec<VirtualQuery>) {
        // Selectors
        let qm = VirtualQuery::new(0, Rotation::curr(), OracleType::Fixed);
        let ql = VirtualQuery::new(1, Rotation::curr(), OracleType::Fixed);
        let qr = VirtualQuery::new(2, Rotation::curr(), OracleType::Fixed);
        let qo = VirtualQuery::new(3, Rotation::curr(), OracleType::Fixed);
        let qpi = VirtualQuery::new(4, Rotation::curr(), OracleType::Fixed);

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
            let qpi: VirtualExpression<F> = qpi.clone().into();

            let pi: VirtualExpression<F> = pi.clone().into();

            let a: VirtualExpression<F> = a.clone().into();
            let b: VirtualExpression<F> = b.clone().into();
            let c: VirtualExpression<F> = c.clone().into();

            a.clone() * b.clone() * qm + a * ql + b * qr + c * qo + pi + qpi
        };

        (plonk_expression, vec![qm, ql, qr, qo, qpi, pi, a, b, c])
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
