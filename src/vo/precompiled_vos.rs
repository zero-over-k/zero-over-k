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

use crate::{oracles::{rotation::Rotation, query::{OracleType, OracleQuery}, traits::ConcreteOracle, instance::InstanceOracle, fixed::FixedOracle}, commitment::HomomorphicCommitment};

use super::{virtual_expression::VirtualExpression, query::VirtualQuery, new_expression::NewExpression, VirtualOracle};

pub trait PrecompiledVO<F: PrimeField> {
    fn get_expr_and_queries() -> (VirtualExpression<F>, Vec<VirtualQuery>);
}

pub struct PrecompiledMul {
}

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

pub struct GenericVO<F: PrimeField> {
    pub(crate) virtual_exp: VirtualExpression<F>, 
    pub(crate) virtual_queries: Vec<VirtualQuery>,
    pub(crate) queries: Option<Vec<OracleQuery>>,
    pub(crate) expression: Option<NewExpression<F>>
}

impl<F: PrimeField> GenericVO<F> {
    pub fn init(cfg: (VirtualExpression<F>, Vec<VirtualQuery>)) -> Self {
        Self {
            virtual_exp: cfg.0, 
            virtual_queries: cfg.1, 
            queries: None, 
            expression: None
        }
    }

    pub fn configure<PC: HomomorphicCommitment<F>>(
        &mut self, 
        witness_oracles: &[impl ConcreteOracle<F>],
        instance_oracles: &[InstanceOracle<F>],
        fixed_oracles: &[FixedOracle<F, PC>]
    ) {
        let mut queries = Vec::with_capacity(self.virtual_queries.len());
        for query in &self.virtual_queries {
            let oracle_query = match query.oracle_type {
                crate::oracles::query::OracleType::Witness => OracleQuery { label: witness_oracles[query.index].get_label(), rotation: query.rotation, oracle_type: OracleType::Witness },
                crate::oracles::query::OracleType::Instance => OracleQuery { label: instance_oracles[query.index].get_label(), rotation: query.rotation, oracle_type: OracleType::Instance },
                crate::oracles::query::OracleType::Fixed => OracleQuery { label: fixed_oracles[query.index].get_label(), rotation: query.rotation, oracle_type: OracleType::Fixed },
            };

            queries.push(oracle_query);
        }

        self.queries = Some(queries.clone());
        self.expression = Some(self.virtual_exp.to_expression(witness_oracles, instance_oracles, fixed_oracles));
    }
}

impl<F: PrimeField> VirtualOracle<F> for GenericVO<F> {
    fn get_queries(&self) -> &[OracleQuery] {
        match &self.queries {
            Some(queries) => &queries,
            None => panic!("Queries are not initialized"),
        }
    }

    fn get_expression(&self) -> &NewExpression<F> {
        match &self.expression {
            Some(expr) => &expr,
            None => panic!("Expression are not initialized"),
        }
    }
}

#[cfg(test)]
mod test {
    use std::collections::BTreeSet;

    use crate::oracles::{witness::WitnessProverOracle, instance::InstanceOracle, fixed::FixedOracle};

    use super::{GenericVO, PrecompiledMul, PrecompiledVO};
    use ark_bls12_381::{Fr as F, Bls12_381};
    use ark_poly::univariate::DensePolynomial;
    use crate::commitment::KZG10;

    type PC = KZG10<Bls12_381>;

    #[test]
    fn test_simple_mul() {
        let mut mul_vo = GenericVO::<F>::init(PrecompiledMul::get_expr_and_queries());

        let a = WitnessProverOracle::<F>{
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
}