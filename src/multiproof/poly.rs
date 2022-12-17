use ark_ff::FftField;
use ark_poly::{univariate::DensePolynomial, UVPolynomial};

// given the x coords construct Li polynomials
pub fn construct_lagrange_basis<F: FftField>(
    evaluation_domain: &[F],
) -> Vec<DensePolynomial<F>> {
    let mut bases = Vec::with_capacity(evaluation_domain.len());
    for (i, x_i) in evaluation_domain.iter().enumerate() {
        let mut l_i = DensePolynomial::from_coefficients_slice(&[F::one()]);
        for (j, elem) in evaluation_domain.iter().enumerate() {
            if j != i {
                let nom = DensePolynomial::from_coefficients_slice(&[
                    -*elem,
                    F::one(),
                ]);
                let denom = *x_i - *elem;

                l_i = &l_i * &(&nom * denom.inverse().unwrap());
            }
        }

        bases.push(l_i);
    }

    bases
}

pub fn construct_vanishing<F: FftField>(
    evaulation_domain: &[F],
) -> DensePolynomial<F> {
    let mut v_h = DensePolynomial::from_coefficients_slice(&[F::one()]);
    for point in evaulation_domain {
        v_h = &v_h
            * &DensePolynomial::from_coefficients_slice(&[-*point, F::one()]);
    }

    v_h
}
