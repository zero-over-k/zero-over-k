use ark_ff::PrimeField;
use ark_poly::EvaluationDomain;

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
