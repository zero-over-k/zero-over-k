use std::collections::BTreeSet;

use ark_ff::{FftField, PrimeField};
use ark_poly::{univariate::DensePolynomial, GeneralEvaluationDomain};
use ark_poly_commit::{LabeledPolynomial, QuerySet};

use crate::{commitment::HomomorphicCommitment, piop::error::Error};

use super::rotation::{Rotation, Sign};

// NOTE: The implementations of all these traits is exactly the same
// for Fixed, Witness and Instance oracles. We should consider adding
// a macro that implements the trait for all structs to reduce dup code.
pub trait ConcreteOracle<F: FftField> {
    fn get_label(&self) -> String;
    fn get_queried_rotations(&self) -> &BTreeSet<Rotation>;
    fn register_rotation(&mut self, rotation: Rotation);
    fn query(&self, challenge: &F) -> Result<F, Error>;

    // NOTE: We always want degree to be calculated same for all types of oracles consider example
    // when some witness poly is just 0, P side will derive different quotient degree then V
    fn get_degree(&self, domain_size: usize) -> usize {
        domain_size - 1
    }
}

pub trait Instantiable<F: FftField>: ConcreteOracle<F> {
    fn polynomial(&self) -> &DensePolynomial<F>;
    fn evals(&self) -> &Vec<F>;
    fn compute_extended_evals(
        &mut self,
        extended_domain: &GeneralEvaluationDomain<F>,
    );
    fn get_extended_coset_evals(&self) -> Result<&Vec<F>, Error>;
    fn to_labeled(&self) -> LabeledPolynomial<F, DensePolynomial<F>>;

    fn query_in_evals_form(&self, lagrange_evals: &[F]) -> F {
        let mut eval = F::zero();
        for (&xi, &li) in self.evals().iter().zip(lagrange_evals.iter()) {
            eval += xi * li;
        }

        eval
    }

    fn query_in_coset(
        &self,
        omega_index: usize,
        rotation: Rotation,
    ) -> Result<F, Error> {
        let extended_coset_evals = self.get_extended_coset_evals()?;
        if rotation.degree == 0 {
            return Ok(extended_coset_evals[omega_index]);
        }
        let extended_domain_size = extended_coset_evals.len();
        let original_domain_size = self.evals().len();
        let scaling_ratio = extended_domain_size / original_domain_size;
        let eval = match &rotation.sign {
            Sign::Plus => {
                extended_coset_evals[(omega_index
                    + rotation.degree * scaling_ratio)
                    % extended_domain_size]
            }
            // TODO: test negative rotations
            Sign::Minus => {
                let index = omega_index as i64
                    - (rotation.degree * scaling_ratio) as i64;
                if index >= 0 {
                    extended_coset_evals[index as usize]
                } else {
                    let move_from_end = (rotation.degree * scaling_ratio
                        - omega_index)
                        % extended_domain_size;
                    extended_coset_evals[extended_domain_size - move_from_end]
                }
            }
        };
        Ok(eval)
    }

    fn query_at_omega_in_original_domain(
        &self,
        omega_index: usize,
        rotation: Rotation,
    ) -> F {
        let evals = self.evals();
        let domain_size = evals.len();
        if rotation.degree == 0 {
            return evals[omega_index];
        }

        match &rotation.sign {
            Sign::Plus => evals[(omega_index + rotation.degree) % domain_size],
            // TODO: test negative rotations
            Sign::Minus => {
                let index = omega_index as i64 - (rotation.degree) as i64;
                if index >= 0 {
                    evals[index as usize]
                } else {
                    let move_from_end =
                        (rotation.degree - omega_index) % domain_size;
                    evals[domain_size - move_from_end]
                }
            }
        }
    }
}

pub trait CommittedOracle<F: PrimeField, PC: HomomorphicCommitment<F>>:
    ConcreteOracle<F>
{
    fn register_commitment(&mut self, c: PC::Commitment);
    fn get_commitment(&self) -> Result<&PC::Commitment, Error>;
}

pub trait WitnessOracle<F: PrimeField>: ConcreteOracle<F> {
    fn should_include_in_copy(&self) -> bool;
}

pub trait InstanceOracle<F: PrimeField>: ConcreteOracle<F> {}

pub trait FixedOracle<F: PrimeField>: ConcreteOracle<F> {}

pub trait QuerySetProvider<F: PrimeField>: ConcreteOracle<F> {
    fn get_query_set(
        &self,
        opening_challenge_label: &str,
        opening_challenge: F,
        omegas: &[F],
    ) -> QuerySet<F> {
        let mut query_set = QuerySet::new();
        for rotation in self.get_queried_rotations() {
            let point_info = rotation.get_point_info(
                opening_challenge_label,
                opening_challenge,
                omegas,
            );
            query_set.insert((self.get_label(), point_info));
        }

        query_set
    }
}
