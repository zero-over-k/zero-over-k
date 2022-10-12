use std::collections::BTreeSet;

use ark_ff::PrimeField;
use ark_poly::{univariate::DensePolynomial, GeneralEvaluationDomain, EvaluationDomain, Polynomial};
use ark_poly_commit::LabeledPolynomial;

use super::{rotation::{Rotation, Sign}, traits::{ConcreteOracle, Instantiable}, query::QueryContext};

#[derive(Clone)]
pub struct InstanceOracle<F: PrimeField> {
    pub(crate) label: String,
    pub(crate) poly: DensePolynomial<F>,
    pub(crate) evals_at_coset_of_extended_domain: Option<Vec<F>>,
    pub(crate) queried_rotations: BTreeSet<Rotation>,
}

impl<F: PrimeField> ConcreteOracle<F> for InstanceOracle<F> {
    fn register_rotation(&mut self, rotation: Rotation) {
        self.queried_rotations.insert(rotation);
    }

    fn get_degree(&self, domain_size: usize) -> usize {
        domain_size - 1
    }

    fn query(&self, ctx: &QueryContext<F>) -> F {
        match ctx {
            QueryContext::Challenge(challenge) => {
                self.poly.evaluate(&challenge)
            },
            QueryContext::ExtendedCoset(original_domain_size, rotation, omega_i) => {
                match &self.evals_at_coset_of_extended_domain {
                    Some(evals) => {
                        if rotation.degree == 0 {
                            return evals[*omega_i];
                        }
                        let extended_domain_size = evals.len();
                        let scaling_ratio = extended_domain_size / original_domain_size;
                        let eval = match &rotation.sign {
                            Sign::Plus => {
                                evals[(omega_i + rotation.degree * scaling_ratio)
                                    % extended_domain_size]
                            }
                            // TODO: test negative rotations
                            Sign::Minus => {
                                let index = *omega_i as i64
                                    - (rotation.degree * scaling_ratio) as i64;
                                if index >= 0 {
                                    evals[index as usize]
                                } else {
                                    let move_from_end =
                                        (rotation.degree * scaling_ratio - omega_i)
                                            % extended_domain_size;
                                    evals[extended_domain_size - move_from_end]
                                }
                            }
                        };
                        return eval;
                    }
                    None => panic!("Evals not provided"),
                }
            },
        }
    }

    fn get_label(&self) -> String {
        self.label.clone()
    }

    fn get_queried_rotations(&self) -> &BTreeSet<Rotation> {
        &self.queried_rotations
    }
}

impl<F: PrimeField> Instantiable<F> for InstanceOracle<F> {
    fn compute_extended_evals(&mut self, extended_domain: &GeneralEvaluationDomain<F>) {
        self.evals_at_coset_of_extended_domain =
            Some(extended_domain.coset_fft(&self.poly));
    }

    fn to_labeled(&self) -> LabeledPolynomial<F, DensePolynomial<F>> {
        LabeledPolynomial::new(
            self.label.clone(),
            self.poly.clone(),
            None,
            None, // blinding is not required for public polynomials
        )
    }

    fn polynomial(&self) -> &DensePolynomial<F> {
        &self.poly
    }
}