use std::{cmp::max, ops::{Neg, Add, Sub, Mul}};

use ark_ff::{Field, PrimeField};

use crate::concrete_oracle::ProverConcreteOracle;

use super::query::{InstanceQuery, WitnessQuery};

#[derive(Clone)]
pub enum Expression<F> {
    Constant(F),
    Instance(InstanceQuery),
    Witness(WitnessQuery),
    Negated(Box<Expression<F>>),
    Sum(Box<Expression<F>>, Box<Expression<F>>),
    Product(Box<Expression<F>>, Box<Expression<F>>),
    Scaled(Box<Expression<F>>, F),
}

impl<F: PrimeField> Expression<F> {
    /// Evaluate expression given generic closures that are provided
    /// When proving evals_at_coset_of_extended_domain can be queried
    /// and when verifying openings and challenges can be used
    #[allow(clippy::too_many_arguments)]
    pub fn evaluate<T>(
        &self,
        wtns_oracles: &[&ProverConcreteOracle<F>],
        instance_oracles: &[&ProverConcreteOracle<F>],
        constant_fn: &impl Fn(F) -> T,
        wtns_fn: &impl Fn(&WitnessQuery, &[&ProverConcreteOracle<F>]) -> T,
        instance_fn: &impl Fn(&InstanceQuery, &[&ProverConcreteOracle<F>]) -> T,
        negated_fn: &impl Fn(T) -> T,
        sum_fn: &impl Fn(T, T) -> T,
        product_fn: &impl Fn(T, T) -> T,
        scaled_fn: &impl Fn(T, F) -> T,
    ) -> T {
        match self {
            Expression::Constant(scalar) => constant_fn(*scalar),
            Expression::Witness(query) => wtns_fn(query, wtns_oracles),
            Expression::Instance(query) => instance_fn(query, instance_oracles),
            Expression::Negated(a) => {
                let a = a.evaluate(
                    wtns_oracles, 
                    instance_oracles,
                    constant_fn,
                    wtns_fn,
                    instance_fn,
                    negated_fn,
                    sum_fn,
                    product_fn,
                    scaled_fn,
                );
                negated_fn(a)
            }
            Expression::Sum(a, b) => {
                let a = a.evaluate(
                    wtns_oracles, 
                    instance_oracles,
                    constant_fn,
                    wtns_fn,
                    instance_fn,
                    negated_fn,
                    sum_fn,
                    product_fn,
                    scaled_fn,
                );
                let b = b.evaluate(
                    wtns_oracles, 
                    instance_oracles,
                    constant_fn,
                    wtns_fn,
                    instance_fn,
                    negated_fn,
                    sum_fn,
                    product_fn,
                    scaled_fn,
                );
                sum_fn(a, b)
            }
            Expression::Product(a, b) => {
                let a = a.evaluate(
                    wtns_oracles, 
                    instance_oracles,
                    constant_fn,
                    wtns_fn,
                    instance_fn,
                    negated_fn,
                    sum_fn,
                    product_fn,
                    scaled_fn,
                );
                let b = b.evaluate(
                    wtns_oracles, 
                    instance_oracles,
                    constant_fn,
                    wtns_fn,
                    instance_fn,
                    negated_fn,
                    sum_fn,
                    product_fn,
                    scaled_fn,
                );
                product_fn(a, b)
            }
            Expression::Scaled(a, f) => {
                let a = a.evaluate(
                    wtns_oracles, 
                    instance_oracles,
                    constant_fn,
                    wtns_fn,
                    instance_fn,
                    negated_fn,
                    sum_fn,
                    product_fn,
                    scaled_fn,
                );
                scaled_fn(a, *f)
            }
        }
    }
    /// Compute the degree of this polynomial
    pub fn degree(
        &self,
        wtns_oracles: &[&ProverConcreteOracle<F>],
        instance_oracles: &[&ProverConcreteOracle<F>]
    ) -> usize {
        match self {
            Expression::Constant(_) => 0,
            Expression::Witness(query) => {
                wtns_oracles[query.index].get_degree()
            },
            Expression::Instance(query) => {
                instance_oracles[query.index].get_degree()
            },
            Expression::Negated(poly) => poly.degree(wtns_oracles, instance_oracles),
            Expression::Sum(a, b) => max(a.degree(wtns_oracles, instance_oracles), b.degree(wtns_oracles, instance_oracles)),
            Expression::Product(a, b) => a.degree(wtns_oracles, instance_oracles) + b.degree(wtns_oracles, instance_oracles),
            Expression::Scaled(poly, _) => poly.degree(wtns_oracles, instance_oracles),
        }
    }
}

impl<F: Field> Neg for Expression<F> {
    type Output = Expression<F>;
    fn neg(self) -> Self::Output {
        Expression::Negated(Box::new(self))
    }
}

impl<F: Field> Add for Expression<F> {
    type Output = Expression<F>;
    fn add(self, rhs: Expression<F>) -> Expression<F> {
        Expression::Sum(Box::new(self), Box::new(rhs))
    }
}

impl<F: Field> Sub for Expression<F> {
    type Output = Expression<F>;
    fn sub(self, rhs: Expression<F>) -> Expression<F> {
        Expression::Sum(Box::new(self), Box::new(-rhs))
    }
}

impl<F: Field> Mul for Expression<F> {
    type Output = Expression<F>;
    fn mul(self, rhs: Expression<F>) -> Expression<F> {
        Expression::Product(Box::new(self), Box::new(rhs))
    }
}

impl<F: Field> Mul<F> for Expression<F> {
    type Output = Expression<F>;
    fn mul(self, rhs: F) -> Expression<F> {
        Expression::Scaled(Box::new(self), rhs)
    }
}

#[cfg(test)]
mod test {
    use crate::{vo::query::{Rotation, WitnessQuery, InstanceQuery, Query}, concrete_oracle::{ProverConcreteOracle, OracleType}};

    use super::Expression;
    use ark_bls12_381::Fr as F;
    use ark_poly::{univariate::DensePolynomial, UVPolynomial};
    use ark_std::test_rng;

    #[test]
    fn test_expression_degree() {
        let mut rng = test_rng();

        let o1 = ProverConcreteOracle {
            label: "o1".to_string(), 
            poly: DensePolynomial::<F>::rand(10, &mut rng),
            evals_at_coset_of_extended_domain: None, 
            oracle_type: OracleType::Witness,
            queried_rotations: vec![],
            should_mask: false
        };

        let o2 = ProverConcreteOracle {
            label: "o2".to_string(), 
            poly: DensePolynomial::<F>::rand(10, &mut rng),
            evals_at_coset_of_extended_domain: None, 
            oracle_type: OracleType::Witness,
            queried_rotations: vec![],
            should_mask: false
        };

        let o3 = ProverConcreteOracle {
            label: "o3".to_string(), 
            poly: DensePolynomial::<F>::rand(10, &mut rng),
            evals_at_coset_of_extended_domain: None, 
            oracle_type: OracleType::Witness,
            queried_rotations: vec![],
            should_mask: false
        };

        let o4 = ProverConcreteOracle {
            label: "o4".to_string(), 
            poly: DensePolynomial::<F>::rand(10, &mut rng),
            evals_at_coset_of_extended_domain: None, 
            oracle_type: OracleType::Instance,
            queried_rotations: vec![],
            should_mask: false
        };

        let o5 = ProverConcreteOracle {
            label: "o5".to_string(), 
            poly: DensePolynomial::<F>::rand(10, &mut rng),
            evals_at_coset_of_extended_domain: None, 
            oracle_type: OracleType::Instance,
            queried_rotations: vec![],
            should_mask: false
        };

        let q1 = WitnessQuery {
            index: 0, 
            rotation: Rotation::curr()
        };

        let q2 = WitnessQuery {
            index: 1, 
            rotation: Rotation::curr()
        };

        let q3 = WitnessQuery {
            index: 2, 
            rotation: Rotation::curr()
        };

        let q4 = InstanceQuery {
            index: 0, 
            rotation: Rotation::curr()
        };

        let q5 = InstanceQuery {
            index: 1, 
            rotation: Rotation::curr()
        };

        let wtns_queries = vec![q1, q2, q3];
        let instance_queries = vec![q4, q5];

        let wtns_oracles = vec![&o1, &o2, &o3];
        let instance_oracles = vec![&o4, &o5];

        let w1 = Expression::<F>::Witness(wtns_queries[0].clone());
        let w2 = Expression::<F>::Witness(wtns_queries[1].clone());
        let w3 = Expression::<F>::Witness(wtns_queries[2].clone());

        let i1 = Expression::<F>::Instance(instance_queries[0].clone());
        let i2 = Expression::<F>::Instance(instance_queries[1].clone());

        let expr = (w1 + w2) * w3 - (i1 * i2);

        assert_eq!(expr.degree(&wtns_oracles, &instance_oracles), 20);

        let poly_by_hand = &(&(o1.poly.clone() + o2.poly.clone()) * &o3.poly) - &(&o4.poly * &o5.poly);

        let constant_fn = |a: F| DensePolynomial::<F>::from_coefficients_slice(&[a]);
        let wtns_fn = |q: &WitnessQuery, oracles: &[&ProverConcreteOracle<F>]| {
            oracles[q.get_index()].poly.clone()
        };
        let instance_fn = |q: &InstanceQuery, oracles: &[&ProverConcreteOracle<F>]| {
            oracles[q.get_index()].poly.clone()
        };
        let negated_fn = |p: DensePolynomial<F>| -p;
        let sum_fn = |a: DensePolynomial<F>, b: DensePolynomial<F>| a + b;
        let product_fn = |a: DensePolynomial<F>, b: DensePolynomial<F>| &a * &b;
        let scaled_fn = |p: DensePolynomial<F>, x: F| &p * x;

        let eval_poly = expr.evaluate::<DensePolynomial<F>>(
            &wtns_oracles, 
            &instance_oracles, 
            &constant_fn, 
            &wtns_fn, 
            &instance_fn, 
            &negated_fn, 
            &sum_fn, 
            &product_fn, 
            &scaled_fn
        );

        assert_eq!(poly_by_hand, eval_poly);

    }
}
