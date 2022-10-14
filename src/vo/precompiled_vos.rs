// use ark_ff::PrimeField;

// use crate::oracles::query::OracleQuery;

// use super::{
//     query::{VirtualQuery},
//     VirtualOracle, new_expression::NewExpression,
// };

// pub struct MulVO<F: PrimeField> {
//     virtual_queries: [VirtualQuery; 3],
//     witness_indices: Option<Vec<usize>>,
//     instance_indices: Option<Vec<usize>>,
//     queries: Vec<OracleQuery>,
//     expression: Option<NewExpression<F>>,
// }

// impl<F: PrimeField> MulVO<F> {
//     pub fn new(virtual_queries: [VirtualQuery; 3]) -> Self {
//         Self {
//             virtual_queries,
//             witness_indices: None,
//             instance_indices: None,
//             queries: vec![],
//             expression: None,
//         }
//     }

//     // TODO: consider abstracting
//     pub fn configure(
//         &mut self,
//         witness_indices: Vec<usize>,
//         instance_indices: Vec<usize>,
//     ) {
//         self.witness_indices = Some(vec![]);
//         self.instance_indices = Some(vec![]);
//         for vq in &self.virtual_queries {
//             match vq.oracle_type {
//                 OracleType::Witness => {
//                     let query = WitnessQuery {
//                         index: witness_indices[vq.index],
//                         rotation: vq.rotation.clone(),
//                     };

//                     self.wtns_queries.push(query);
//                     self.queries.push(Box::new(query.clone()))
//                 },
//                 OracleType::Instance => {
//                     let query = InstanceQuery {
//                         index: instance_indices[vq.index],
//                         rotation: vq.rotation.clone(),
//                     };

//                     self.instance_queries.push(query);
//                     self.queries.push(Box::new(query.clone()))
//                 }
//             }
//         }

//         let mul_expression = || {
//             let a: Expression<F> = self.wtns_queries[0].into();
//             let b: Expression<F> = self.wtns_queries[1].into();
//             let c: Expression<F> = self.instance_queries[0].into();

//             a * b - c
//         };

//         self.expression = Some(mul_expression());
//     }
// }

// impl<F: PrimeField> VirtualOracle<F> for MulVO<F> {
//     fn get_wtns_queries(&self) -> &[WitnessQuery] {
//         &self.wtns_queries
//     }

//     fn get_instance_queries(&self) -> &[InstanceQuery] {
//         &self.instance_queries
//     }

//     // panics if expression is not defined before proving started
//     fn get_expression(&self) -> &Expression<F> {
//         match self.expression.as_ref() {
//             None => panic!("Expression is not defined"),
//             Some(expression) => return expression,
//         }
//     }

//     fn get_queries(&self) -> &[Box<dyn Query>] {
//         &self.queries
//     }
// }

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
            fixed::FixedOracle, instance::InstanceOracle,
            witness::WitnessProverOracle,
        },
        vo::generic_vo::GenericVO,
    };

    use super::{PrecompiledMul, PrecompiledRescue, PrecompiledVO};
    use crate::commitment::KZG10;
    use ark_bls12_381::{Bls12_381, Fr as F};
    use ark_poly::univariate::DensePolynomial;

    type PC = KZG10<Bls12_381>;

    #[test]
    fn test_simple_mul() {
        let mut mul_vo =
            GenericVO::<F>::init(PrecompiledMul::get_expr_and_queries());

        let a = WitnessProverOracle::<F> {
            label: "a".to_string(),
            poly: DensePolynomial::default(),
            evals_at_coset_of_extended_domain: None,
            queried_rotations: BTreeSet::new(),
            should_mask: true,
        };

        let b = WitnessProverOracle::<F> {
            label: "b".to_string(),
            poly: DensePolynomial::default(),
            evals_at_coset_of_extended_domain: None,
            queried_rotations: BTreeSet::new(),
            should_mask: true,
        };

        let c = InstanceOracle::<F> {
            label: "c".to_string(),
            poly: DensePolynomial::default(),
            evals_at_coset_of_extended_domain: None,
            queried_rotations: BTreeSet::new(),
        };

        let witness_oracles = vec![a, b];
        let instance_oracles = vec![c];
        let fixed_oracles: Vec<FixedOracle<F, PC>> = vec![];

        mul_vo.configure(&witness_oracles, &instance_oracles, &fixed_oracles);
    }

    #[test]
    fn test_rescue_gate() {
        let mut rescue_vo =
            GenericVO::<F>::init(PrecompiledRescue::get_expr_and_queries());

        let witness_oracles: Vec<_> = ["a", "b", "c", "d", "e"]
            .into_iter()
            .map(|label| WitnessProverOracle::<F> {
                label: label.to_string(),
                poly: DensePolynomial::default(),
                evals_at_coset_of_extended_domain: None,
                queried_rotations: BTreeSet::new(),
                should_mask: true,
            })
            .collect();

        let instance_oracles = vec![];

        let fixed_oracles: Vec<_> = ["q1", "q2", "q3", "q4"]
            .into_iter()
            .map(|label| FixedOracle::<F, PC> {
                label: label.to_string(),
                poly: DensePolynomial::default(),
                evals_at_coset_of_extended_domain: None,
                queried_rotations: BTreeSet::default(),
                evals_at_challenges: BTreeMap::default(),
                commitment: None,
            })
            .collect();

        rescue_vo.configure(
            &witness_oracles,
            &instance_oracles,
            &fixed_oracles,
        );
    }
}
