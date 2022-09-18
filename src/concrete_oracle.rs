use crate::{
    error::Error,
    vo::query::{Rotation, Sign},
};
use ark_ff::PrimeField;
use ark_poly::{
    univariate::DensePolynomial, EvaluationDomain, GeneralEvaluationDomain, Polynomial,
    UVPolynomial,
};

use ark_poly_commit::QuerySet;
use ark_std::rand::Rng;

pub trait QuerySetProvider<F: PrimeField> {
    fn get_query_set(
        &self,
        opening_challenge_label: &str,
        opening_challenge: F,
        domain_size: usize,
    ) -> QuerySet<F>;
}

#[derive(PartialEq, PartialOrd, Eq, Ord, Clone)]
pub enum OracleType {
    Witness,
    Instance,
}

// Note: We keep masking as flexible even when concrete oracle is of type witness
// In halo2 for example, wires are being masked with randomizing last m rows

/// Concrete oracle definition
#[derive(Clone)]
pub struct ProverConcreteOracle<F: PrimeField> {
    pub(crate) label: String,
    pub(crate) poly: DensePolynomial<F>,
    pub(crate) evals_at_coset_of_extended_domain: Option<Vec<F>>,
    pub(crate) oracle_type: OracleType,
    pub(crate) queried_rotations: Vec<Rotation>,
    pub(crate) should_mask: bool,
}

impl<F: PrimeField> ProverConcreteOracle<F> {
    pub fn mask<R: Rng>(&mut self, vanishing_polynomial: &DensePolynomial<F>, rng: &mut R) {
        if !self.should_mask {
            return;
        }

        let masking = DensePolynomial::rand(self.queried_rotations.len(), rng);
        self.poly += &(vanishing_polynomial * &masking);
    }

    pub fn register_rotation(&mut self, rotation: Rotation) {
        // TOTO: maybe we should check for rotation uniqueness also here
        self.queried_rotations.push(rotation);
    }

    pub fn compute_extended_evals(&mut self, extended_domain: GeneralEvaluationDomain<F>) {
        self.evals_at_coset_of_extended_domain = Some(extended_domain.coset_fft(&self.poly));
    }

    pub fn query_in_instantiation_context(
        &self,
        rotation: &Rotation,
        row: usize,
        scaling_ratio: usize,
        extended_domain_size: usize,
    ) -> Result<F, Error> {
        if let Some(evals) = &self.evals_at_coset_of_extended_domain {
            if rotation.degree == 0 {
                return Ok(evals[row]);
            }

            let eval = match &rotation.sign {
                Sign::Plus => evals[(row + rotation.degree * scaling_ratio) % extended_domain_size],
                // TODO: test negative rotations
                Sign::Minus => {
                    let index = row as i64 - (rotation.degree * scaling_ratio) as i64;
                    if index >= 0 {
                        evals[index as usize]
                    } else {
                        let move_from_end =
                            (rotation.degree * scaling_ratio - row) % extended_domain_size;
                        evals[extended_domain_size - move_from_end]
                    }
                }
            };
            return Ok(eval);
        } else {
            return Err(Error::ExtendedEvalsMissing);
        }
    }

    pub fn query_in_opening_context(
        &self,
        rotation: &Rotation,
        challenge: &F,
        domain_size: usize,
    ) -> Result<F, Error> {
        let domain = GeneralEvaluationDomain::<F>::new(domain_size).unwrap();
        if rotation.degree == 0 {
            return Ok(self.poly.evaluate(challenge));
        }

        let mut omega = domain.element(rotation.degree);
        if rotation.sign == Sign::Minus {
            omega = omega.inverse().unwrap();
        }

        Ok(self.poly.evaluate(&(omega * challenge)))
    }

    pub fn get_degree(&self) -> usize {
        self.poly.degree()
    }
}

impl<F: PrimeField> QuerySetProvider<F> for ProverConcreteOracle<F> {
    fn get_query_set(
        &self,
        opening_challenge_label: &str,
        opening_challenge: F,
        domain_size: usize,
    ) -> QuerySet<F> {
        let mut query_set = QuerySet::new();
        for rotation in &self.queried_rotations {
            if rotation.degree == 0 {
                query_set.insert((
                    self.label.clone(),
                    (opening_challenge_label.into(), opening_challenge),
                ));
            } else {
                let domain = GeneralEvaluationDomain::<F>::new(domain_size).unwrap();
                let (omega, point_label) = match &rotation.sign {
                    Sign::Plus => {
                        let omega = domain.element(rotation.degree);
                        let point_label =
                            format!("omega^{}_{}", rotation.degree, opening_challenge_label);
                        (omega, point_label)
                    }
                    Sign::Minus => {
                        let omega = domain.element(rotation.degree).inverse().unwrap();
                        let point_label =
                            format!("omega^(-{})_{}", rotation.degree, opening_challenge_label);
                        (omega, point_label)
                    }
                };

                let point = omega * opening_challenge;
                query_set.insert((self.label.clone(), (point_label, point)));
            }
        }
        query_set
    }
}
