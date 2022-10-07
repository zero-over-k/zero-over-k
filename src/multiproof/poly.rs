use ark_ff::FftField;
use ark_poly::{univariate::DensePolynomial, UVPolynomial};

// given the x coords construct Li polynomials
pub fn construct_lagrange_basis<F: FftField>(
    evaluation_domain: &[F],
) -> Vec<DensePolynomial<F>> {
    let mut bases = Vec::with_capacity(evaluation_domain.len());
    for i in 0..evaluation_domain.len() {
        let mut l_i = DensePolynomial::from_coefficients_slice(&[F::one()]);
        let x_i = evaluation_domain[i];
        for j in 0..evaluation_domain.len() {
            if j != i {
                let nom = DensePolynomial::from_coefficients_slice(&[
                    -evaluation_domain[j],
                    F::one(),
                ]);
                let denom = x_i - evaluation_domain[j];

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
