use std::{
    cmp::max,
    ops::{Add, Mul, Neg, Sub},
};

use ark_ff::{Field, PrimeField};
use ark_poly::univariate::DensePolynomial;
use super::{query::{InstanceQuery, WitnessQuery, self}, linearisation::LinearisationOracleQuery};

#[derive(Clone)]
pub enum Expression<F> {
    Constant(F),
    Instance(InstanceQuery),
    Witness(WitnessQuery),
    Negated(Box<Expression<F>>),
    Sum(Box<Expression<F>>, Box<Expression<F>>),
    Product(Box<Expression<F>>, Box<Expression<F>>),
    Scaled(Box<Expression<F>>, F),

    Linearisation(LinearisationOracleQuery)
}

impl<F: PrimeField> Expression<F> {
    /// Evaluate expression given generic closures that are provided
    /// When proving evals_at_coset_of_extended_domain can be queried
    /// and when verifying openings and challenges can be used
    #[allow(clippy::too_many_arguments)]
    pub fn evaluate<T>(
        &self,
        constant_fn: &impl Fn(F) -> T,
        wtns_fn: &impl Fn(&WitnessQuery) -> T,
        instance_fn: &impl Fn(&InstanceQuery) -> T,
        negated_fn: &impl Fn(T) -> T,
        sum_fn: &impl Fn(T, T) -> T,
        product_fn: &impl Fn(T, T) -> T,
        scaled_fn: &impl Fn(T, F) -> T,

        linearisation_fn: &impl Fn(&LinearisationOracleQuery) -> T,
    ) -> T {
        match self {
            Expression::Constant(scalar) => constant_fn(*scalar),
            Expression::Witness(query) => wtns_fn(query),
            Expression::Instance(query) => instance_fn(query),
            Expression::Negated(a) => {
                let a = a.evaluate(
                    constant_fn,
                    wtns_fn,
                    instance_fn,
                    negated_fn,
                    sum_fn,
                    product_fn,
                    scaled_fn,

                    linearisation_fn
                );
                negated_fn(a)
            }
            Expression::Sum(a, b) => {
                let a = a.evaluate(
                    constant_fn,
                    wtns_fn,
                    instance_fn,
                    negated_fn,
                    sum_fn,
                    product_fn,
                    scaled_fn,

                    linearisation_fn
                );
                let b = b.evaluate(
                    constant_fn,
                    wtns_fn,
                    instance_fn,
                    negated_fn,
                    sum_fn,
                    product_fn,
                    scaled_fn,

                    linearisation_fn
                );
                sum_fn(a, b)
            }
            Expression::Product(a, b) => {
                let a = a.evaluate(
                    constant_fn,
                    wtns_fn,
                    instance_fn,
                    negated_fn,
                    sum_fn,
                    product_fn,
                    scaled_fn,

                    linearisation_fn
                );
                let b = b.evaluate(
                    constant_fn,
                    wtns_fn,
                    instance_fn,
                    negated_fn,
                    sum_fn,
                    product_fn,
                    scaled_fn,

                    linearisation_fn
                );
                product_fn(a, b)
            }
            Expression::Scaled(a, f) => {
                let a = a.evaluate(
                    constant_fn,
                    wtns_fn,
                    instance_fn,
                    negated_fn,
                    sum_fn,
                    product_fn,
                    scaled_fn,

                    linearisation_fn
                );
                scaled_fn(a, *f)
            }
            Expression::Linearisation(query) => {
                linearisation_fn(query)
            }
        }
    }
    /// Compute the degree of this polynomial
    pub fn degree(
        &self,
        wtns_fn: &impl Fn(&WitnessQuery) -> usize,
        instance_fn: &impl Fn(&InstanceQuery) -> usize,
    ) -> usize {
        match self {
            Expression::Constant(_) => 0,
            Expression::Witness(query) => wtns_fn(query),
            Expression::Instance(query) => instance_fn(query),
            Expression::Negated(poly) => poly.degree(wtns_fn, instance_fn),
            Expression::Sum(a, b) => max(
                a.degree(wtns_fn, instance_fn),
                b.degree(wtns_fn, instance_fn),
            ),
            Expression::Product(a, b) => {
                a.degree(wtns_fn, instance_fn) + b.degree(wtns_fn, instance_fn)
            }
            Expression::Scaled(poly, _) => poly.degree(wtns_fn, instance_fn),
            Expression::Linearisation(_) => panic!("skip degree for now")
        }
    }
}

impl<F: PrimeField> Neg for Expression<F> {
    type Output = Expression<F>;
    fn neg(self) -> Self::Output {
        Expression::Negated(Box::new(self))
    }
}

impl<F: PrimeField> Add for Expression<F> {
    type Output = Expression<F>;
    fn add(self, rhs: Expression<F>) -> Expression<F> {
        Expression::Sum(Box::new(self), Box::new(rhs))
    }
}

impl<F: PrimeField> Sub for Expression<F> {
    type Output = Expression<F>;
    fn sub(self, rhs: Expression<F>) -> Expression<F> {
        Expression::Sum(Box::new(self), Box::new(-rhs))
    }
}

impl<F: PrimeField> Mul for Expression<F> {
    type Output = Expression<F>;
    fn mul(self, rhs: Expression<F>) -> Expression<F> {
        Expression::Product(Box::new(self), Box::new(rhs))
    }
}

impl<F: PrimeField> Mul<F> for Expression<F> {
    type Output = Expression<F>;
    fn mul(self, rhs: F) -> Expression<F> {
        Expression::Scaled(Box::new(self), rhs)
    }
}

impl<F: PrimeField> From<WitnessQuery> for Expression<F> {
    fn from(query: WitnessQuery) -> Self {
        Self::Witness(query)
    }
}

impl<F: PrimeField> From<InstanceQuery> for Expression<F> {
    fn from(query: InstanceQuery) -> Self {
        Self::Instance(query)
    }
}

impl<F: PrimeField> From<LinearisationOracleQuery> for Expression<F> {
    fn from(query: LinearisationOracleQuery) -> Self {
        Self::Linearisation(query)
    }
}

/* Linearisation Part */

// pub enum OracleQueryResult<F: PrimeField> {
//     Poly(DensePolynomial<F>),
//     Opening(F)
// }

#[cfg(test)]
mod test {
    use std::collections::BTreeSet;

    use crate::{
        concrete_oracle::{OracleType, ProverConcreteOracle},
        vo::{query::{InstanceQuery, Query, Rotation, WitnessQuery}, linearisation::{LinearisationOracleQuery, LinearisationQueryContext, LinearisationQueriable, LinearisationQueryResponse, LinearisationInfo}},
    };

    use crate::commitment::KZG10;

    use super::Expression;
    use ark_bls12_381::{Fr as F, Bls12_381};
    use ark_ff::{UniformRand, Zero};
    use ark_poly::{univariate::DensePolynomial, UVPolynomial, Polynomial};
    use ark_poly_commit::marlin_pc::MarlinKZG10;
    use ark_std::test_rng;

    type PC = KZG10<Bls12_381>;

    #[test]
    fn test_linearisation() {
        // a * b - c => L = a * [b] - [c]: we open just a and L instead of a, b, c
        let mut rng = test_rng();

        let domain_size = 16;
        let poly_degree = domain_size - 1;

        let a = ProverConcreteOracle {
            label: "a".to_string(),
            poly: DensePolynomial::<F>::rand(poly_degree, &mut rng),
            evals_at_coset_of_extended_domain: None,
            oracle_type: OracleType::Witness,
            queried_rotations: BTreeSet::new(),
            should_mask: false,
        };

        let b = ProverConcreteOracle {
            label: "b".to_string(),
            poly: DensePolynomial::<F>::rand(poly_degree, &mut rng),
            evals_at_coset_of_extended_domain: None,
            oracle_type: OracleType::Witness,
            queried_rotations: BTreeSet::new(),
            should_mask: false,
        };

        let c = ProverConcreteOracle {
            label: "c".to_string(),
            poly: DensePolynomial::<F>::rand(poly_degree, &mut rng),
            evals_at_coset_of_extended_domain: None,
            oracle_type: OracleType::Witness,
            queried_rotations: BTreeSet::new(),
            should_mask: false,
        };

        let opening_challenge = F::rand(&mut rng);

        let wtns_oracles = vec![a.clone(), b.clone(), c.clone()];
        let instance_oracles: Vec<ProverConcreteOracle<F>> = vec![];

        let q1: Expression<F> = LinearisationOracleQuery {
            index: 0, 
            rotation: Rotation::curr(), 
            oracle_type: OracleType::Witness, 
            ctx: LinearisationQueryContext::AsEval
        }.into();

        let q2: Expression<F> = LinearisationOracleQuery {
            index: 1, 
            rotation: Rotation::curr(), 
            oracle_type: OracleType::Witness, 
            ctx: LinearisationQueryContext::AsPoly
        }.into();

        let q3: Expression<F> = LinearisationOracleQuery {
            index: 2, 
            rotation: Rotation::curr(), 
            oracle_type: OracleType::Witness, 
            ctx: LinearisationQueryContext::AsPoly
        }.into();

        let info = LinearisationInfo {
            domain_size, 
            opening_challenge
        };

        let expr_to_linearise = q1 * q2 - q3;

        let vo_evaluation = expr_to_linearise.evaluate::<DensePolynomial<F>>(
            &|x: F| DensePolynomial::from_coefficients_slice(&[x]),
            &|_: &WitnessQuery| {
                // let oracle = &state.witness_oracles[query.get_index()];
                // oracle.query(&query.rotation, &query_context)
                panic!("Not allowed here")
            },
            &|_: &InstanceQuery| {
                // let oracle = &state.instance_oracles[query.get_index()];
                // oracle.query(&query.rotation, &query_context)
                panic!("Not allowed here")
            },
            &|x: DensePolynomial<F>| -x,
            &|x: DensePolynomial<F>, y: DensePolynomial<F>| x + y,
            &|x: DensePolynomial<F>, y: DensePolynomial<F>| &x * &y,
            &|x: DensePolynomial<F>, y: F| &x * y,

            &|query: &LinearisationOracleQuery| {
                let query_response: LinearisationQueryResponse<F, PC> = match query.oracle_type {
                    OracleType::Witness => { 
                        wtns_oracles[query.index].query_for_linearisation(&query.rotation, &query.ctx, &info)
                    }
                    OracleType::Instance => {
                        instance_oracles[query.index].query_for_linearisation(&query.rotation, &query.ctx, &info)
                    }
                };

                match query_response {
                    LinearisationQueryResponse::Opening(x) => DensePolynomial::from_coefficients_slice(&[x]),
                    LinearisationQueryResponse::Poly(poly) => poly,
                    LinearisationQueryResponse::Commitment(_) => panic!("commitment not allowed here"),
                }
            }
        );

        let oracle_by_hand = &(&a.poly * &b.poly) - &c.poly;

        assert_eq!(oracle_by_hand.evaluate(&opening_challenge), vo_evaluation.evaluate(&opening_challenge));


    }
}
