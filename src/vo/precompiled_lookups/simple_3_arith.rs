use std::marker::PhantomData;

use ark_ff::PrimeField;

use crate::{
    oracles::{query::OracleType, rotation::Rotation},
    vo::{query::VirtualQuery, virtual_expression::VirtualExpression},
};

use super::PrecompiledLookupVO;

pub struct PrecompiledSimple3ArithLookup<F: PrimeField> {
    _f: PhantomData<F>,
}

impl<F: PrimeField> PrecompiledLookupVO<F>
    for PrecompiledSimple3ArithLookup<F>
{
    fn get_expressions_and_queries() -> (
        Vec<crate::vo::virtual_expression::VirtualExpression<F>>,
        Vec<crate::vo::query::VirtualQuery>,
        Vec<crate::vo::query::VirtualQuery>,
    ) {
        let q1 = VirtualQuery::new(0, Rotation::curr(), OracleType::Witness);
        let q2 = VirtualQuery::new(1, Rotation::curr(), OracleType::Witness);
        let q3 = VirtualQuery::new(2, Rotation::curr(), OracleType::Witness);

        let t_q1 = VirtualQuery::new(0, Rotation::curr(), OracleType::Fixed);
        let t_q2 = VirtualQuery::new(1, Rotation::curr(), OracleType::Fixed);
        let t_q3 = VirtualQuery::new(2, Rotation::curr(), OracleType::Fixed);

        let expr1: VirtualExpression<F> = q1.clone().into();
        let expr2: VirtualExpression<F> = q2.clone().into();
        let expr3: VirtualExpression<F> = q3.clone().into();

        let expressions = vec![expr1, expr2, expr3];
        let queries = vec![q1, q2, q3];
        let table_queries = vec![t_q1, t_q2, t_q3];

        (expressions, queries, table_queries)
    }
}

#[cfg(test)]
mod test {
    use std::collections::BTreeSet;

    use ark_ff::Zero;
    use ark_poly::univariate::DensePolynomial;

    use crate::{
        oracles::{
            fixed::FixedProverOracle, instance::InstanceProverOracle,
            witness::WitnessProverOracle,
        },
        vo::{
            generic_lookup_vo::GenericLookupVO,
            precompiled_lookups::PrecompiledLookupVO,
        },
    };

    use super::PrecompiledSimple3ArithLookup;

    use crate::commitment::KZG10;
    use ark_bls12_381::{Bls12_381, Fr as F};

    #[test]
    fn test_simple_lookup_configuration() {
        let mut a = WitnessProverOracle {
            label: "a".to_string(),
            poly: DensePolynomial::zero(),
            evals: vec![],
            evals_at_coset_of_extended_domain: None,
            queried_rotations: BTreeSet::default(),
            should_permute: false,
        };

        let mut b = WitnessProverOracle {
            label: "b".to_string(),
            poly: DensePolynomial::zero(),
            evals: vec![],
            evals_at_coset_of_extended_domain: None,
            queried_rotations: BTreeSet::default(),
            should_permute: false,
        };

        let mut c = WitnessProverOracle {
            label: "c".to_string(),
            poly: DensePolynomial::zero(),
            evals: vec![],
            evals_at_coset_of_extended_domain: None,
            queried_rotations: BTreeSet::default(),
            should_permute: false,
        };

        let t1 = FixedProverOracle {
            label: "t1".to_string(),
            poly: DensePolynomial::zero(),
            evals: vec![],
            evals_at_coset_of_extended_domain: None,
            queried_rotations: BTreeSet::default(),
        };

        let t2 = FixedProverOracle {
            label: "t2".to_string(),
            poly: DensePolynomial::zero(),
            evals: vec![],
            evals_at_coset_of_extended_domain: None,
            queried_rotations: BTreeSet::default(),
        };

        let t3 = FixedProverOracle {
            label: "t3".to_string(),
            poly: DensePolynomial::zero(),
            evals: vec![],
            evals_at_coset_of_extended_domain: None,
            queried_rotations: BTreeSet::default(),
        };

        let mut simple_lookup_vo = GenericLookupVO::<F>::init(
            PrecompiledSimple3ArithLookup::get_expressions_and_queries(),
        );

        let mut witness_oracles: &mut [&mut WitnessProverOracle<F>] = &mut [&mut a, &mut b, &mut c];
        let mut instance_oracles: Vec<InstanceProverOracle<F>> = vec![];
        let mut fixed_oracles = &mut [] as &mut [&mut FixedProverOracle<F>];

        let mut table_oracles = vec![t1, t2, t3];

        simple_lookup_vo.configure(
            &mut witness_oracles,
            &mut instance_oracles,
            &mut fixed_oracles,
            &mut table_oracles,
        );
    }
}
