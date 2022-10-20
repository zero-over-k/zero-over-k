use std::collections::BTreeMap;

use ark_ff::{Field, PrimeField};
use ark_poly::{univariate::DensePolynomial, EvaluationDomain, Polynomial};
use ark_poly_commit::{LabeledPolynomial, QuerySet};

pub fn compute_vanishing_poly_over_coset<F, D>(
    domain: D,        // domain to evaluate over
    poly_degree: u64, // degree of the vanishing polynomial
) -> Vec<F>
where
    F: PrimeField,
    D: EvaluationDomain<F>,
{
    assert!(
        (domain.size() as u64) > poly_degree,
        "domain_size = {}, poly_degree = {}",
        domain.size() as u64,
        poly_degree
    );
    let group_gen = domain.element(1);
    let coset_gen = F::multiplicative_generator().pow(&[poly_degree, 0, 0, 0]);
    let v_h: Vec<_> = (0..domain.size())
        .map(|i| {
            (coset_gen * group_gen.pow(&[poly_degree * i as u64, 0, 0, 0]))
                - F::one()
        })
        .collect();
    v_h
}

/// Evaluate the given polynomials at `query_set`.
/// We can't use arkworks evaluate_query_set because iterating throw evaluations and collecting it into just evals is reordering array
pub fn evaluate_q_set<'a, F: PrimeField>(
    polys: impl IntoIterator<Item = &'a LabeledPolynomial<F, DensePolynomial<F>>>,
    query_set: &QuerySet<F>,
) -> Vec<F> {
    let polys = BTreeMap::from_iter(polys.into_iter().map(|p| (p.label(), p)));
    let mut evaluations = vec![];
    for (label, (point_label, point)) in query_set {
        let poly = polys
            .get(label)
            .expect("polynomial in evaluated lc is not found");
        let eval = poly.evaluate(&point);
        // evaluations.insert((label.clone(), point.clone()), eval);
        println!(
            "poly: {} in point: {} evaluates to: {}",
            label, point_label, eval
        );
        evaluations.push(eval);
    }
    evaluations
}
