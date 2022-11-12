#[cfg(test)]
mod test {
    use ark_bls12_381::Fr as F;
    use ark_ff::{One, Zero};
    use ark_poly::{
        univariate::DensePolynomial, EvaluationDomain, GeneralEvaluationDomain,
        Polynomial, UVPolynomial,
    };

    #[test]
    fn works() {
        // TODO: enable fast lagrange evaluation
        let domain_size = 8;
        let domain = GeneralEvaluationDomain::<F>::new(domain_size).unwrap();
        let mut l0_evals = vec![F::zero(); domain_size];
        l0_evals[1] = F::one();
        let l0 =
            DensePolynomial::from_coefficients_slice(&domain.ifft(&l0_evals));

        let ch = F::from(1231u64);
        println!("eval: {}", l0.evaluate(&ch));
    }
}
