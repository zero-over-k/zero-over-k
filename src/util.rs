use std::collections::BTreeMap;

use ark_ff::PrimeField;
use ark_poly::EvaluationDomain;
use ark_poly_commit::QuerySet;

use crate::oracles::traits::Instantiable;
use crate::piop::error::Error as PiopError;

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
    let coset_gen = F::multiplicative_generator().pow([poly_degree, 0, 0, 0]);
    let v_h: Vec<_> = (0..domain.size())
        .map(|i| {
            (coset_gen * group_gen.pow([poly_degree * i as u64, 0, 0, 0]))
                - F::one()
        })
        .collect();
    v_h
}

/// Evaluate the given polynomials at `query_set`.
/// We can't use arkworks evaluate_query_set because iterating throw evaluations and collecting it into just evals is reordering array
pub fn evaluate_query_set<'a, F: PrimeField>(
    polys: &[impl Instantiable<F>],
    query_set: &QuerySet<F>,
) -> Result<Vec<F>, PiopError> {
    let oracles =
        BTreeMap::from_iter(polys.iter().map(|p| (p.get_label(), p)));
    let mut evaluations = vec![];
    for (label, (_, point)) in query_set {
        let oracle = oracles.get(label).unwrap_or_else(|| panic!("Evaluating Query Set: oracle with label {} not found",
                label));
        evaluations.push(oracle.query(point)?);
    }
    Ok(evaluations)
}
