use std::collections::{BTreeMap, BTreeSet};

use crate::{
    commitment::HomomorphicCommitment,
    vo::{
        linearisation::{
            LinearisationInfo, LinearisationQueriable,
            LinearisationQueryContext, LinearisationQueryResponse,
        },
        query::{Rotation, Sign},
    },
};
use ark_ff::{Field, PrimeField};
use ark_poly::{
    univariate::DensePolynomial, EvaluationDomain, GeneralEvaluationDomain,
    Polynomial, UVPolynomial,
};

use ark_poly_commit::{LabeledPolynomial, PolynomialCommitment, QuerySet};
use ark_std::rand::Rng;

pub trait QuerySetProvider<F: PrimeField> {
    fn get_query_set(
        &self,
        opening_challenge_label: &str,
        opening_challenge: F,
        domain_size: usize,
    ) -> QuerySet<F>;

    fn get_point_info(
        &self,
        opening_challenge_label: &str,
        opening_challenge: F,
        omegas: &Vec<F>,
        rotation: Rotation,
    ) -> (String, F) {

        if rotation.degree == 0 {
            return (opening_challenge_label.into(), opening_challenge)
        } else {
            let (omega, point_label) = match &rotation.sign {
                Sign::Plus => {
                    let omega = omegas[rotation.degree];
                    let point_label = format!(
                        "omega_{}_{}",
                        rotation.degree, opening_challenge_label
                    );
                    (omega, point_label)
                }
                Sign::Minus => {
                    let omega =
                        omegas[rotation.degree].inverse().unwrap();
                    let point_label = format!(
                        "omega_-{}_{}",
                        rotation.degree, opening_challenge_label
                    );
                    (omega, point_label)
                }
            };

            let point = omega * opening_challenge;
            (point_label, point)
        }
    }
}
#[derive(Debug)]
pub enum QueryPoint<F: PrimeField> {
    Omega(usize),
    Challenge(F),
}

type ScalingRatio = usize;
type ExtendedDomainSize = usize;
pub type DomainSize = usize;
pub enum QueryContext<F: PrimeField> {
    Instantiation(ScalingRatio, ExtendedDomainSize, QueryPoint<F>),
    Opening(DomainSize, QueryPoint<F>),
}

impl<F: PrimeField> QueryPoint<F> {
    pub fn replace_omega(&mut self, new_row: usize) {
        match self {
            Self::Omega(row) => {
                let _ = std::mem::replace(row, new_row);
            }
            Self::Challenge(_) => {
                panic!("Wrong point type")
            }
        }
    }
}

impl<F: PrimeField> QueryContext<F> {
    pub fn replace_omega(&mut self, new_row: usize) {
        match self {
            Self::Instantiation(_, _, point) => {
                point.replace_omega(new_row);
            }
            Self::Opening(_, _) => {
                panic!("Wrong context")
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::QueryPoint;
    use ark_bls12_381::Fr as F;

    #[test]
    fn test_replace() {
        let mut point = QueryPoint::<F>::Omega(1);

        for i in 0..5 {
            point.replace_omega(i);
        }

        println!("{:?}", point);
    }
}

pub trait Queriable<F: PrimeField> {
    fn query(&self, rotation: &Rotation, context: &QueryContext<F>) -> F;
}

// TODO: add shared functionalities in trait
pub trait ConcreteOracle {}

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
    pub(crate) queried_rotations: BTreeSet<Rotation>,
    pub(crate) should_mask: bool,
}

impl<F: PrimeField> ProverConcreteOracle<F> {
    pub fn mask<R: Rng>(
        &mut self,
        vanishing_polynomial: &DensePolynomial<F>,
        rng: &mut R,
    ) {
        if !self.should_mask {
            return;
        }

        let masking = DensePolynomial::rand(self.queried_rotations.len(), rng);
        self.poly += &(vanishing_polynomial * &masking);
    }

    pub fn register_rotation(&mut self, rotation: Rotation) {
        // TOTO: maybe we should check for rotation uniqueness also here
        self.queried_rotations.insert(rotation);
    }

    pub fn compute_extended_evals(
        &mut self,
        extended_domain: GeneralEvaluationDomain<F>,
    ) {
        self.evals_at_coset_of_extended_domain =
            Some(extended_domain.coset_fft(&self.poly));
    }

    pub fn get_degree(&self) -> usize {
        self.poly.degree()
    }

    pub fn to_labeled(&self) -> LabeledPolynomial<F, DensePolynomial<F>> {
        // for now keep degree bound and hiding bound to None
        LabeledPolynomial::new(
            self.label.clone(),
            self.poly.clone(),
            None,
            None,
        )
    }
}

impl<F: PrimeField> Queriable<F> for ProverConcreteOracle<F> {
    fn query(&self, rotation: &Rotation, context: &QueryContext<F>) -> F {
        match context {
            QueryContext::Instantiation(
                scaling_ratio,
                extended_domain_size,
                point,
            ) => {
                match point {
                    QueryPoint::Omega(row) => {
                        if let Some(evals) =
                            &self.evals_at_coset_of_extended_domain
                        {
                            if rotation.degree == 0 {
                                return evals[*row];
                            }

                            let eval = match &rotation.sign {
                                Sign::Plus => {
                                    evals[(row
                                        + rotation.degree * scaling_ratio)
                                        % extended_domain_size]
                                }
                                // TODO: test negative rotations
                                Sign::Minus => {
                                    let index = *row as i64
                                        - (rotation.degree * scaling_ratio)
                                            as i64;
                                    if index >= 0 {
                                        evals[index as usize]
                                    } else {
                                        let move_from_end = (rotation.degree
                                            * scaling_ratio
                                            - row)
                                            % extended_domain_size;
                                        evals[extended_domain_size
                                            - move_from_end]
                                    }
                                }
                            };
                            return eval;
                        } else {
                            // return Err(Error::ExtendedEvalsMissing);
                            panic!("Extended Evals Missing")
                        }
                    }
                    QueryPoint::Challenge(_) => {
                        panic!("Can't evaluate at challenge in instantiation context");
                    }
                }
            }
            QueryContext::Opening(domain_size, point) => match point {
                QueryPoint::Omega(_) => {
                    panic!("Can't evaluate at row_i in opening context");
                }
                QueryPoint::Challenge(challenge) => {
                    if rotation.degree == 0 {
                        return self.poly.evaluate(&challenge);
                    }

                    let domain =
                        GeneralEvaluationDomain::<F>::new(*domain_size)
                            .unwrap();

                    let mut omega = domain.element(rotation.degree);
                    if rotation.sign == Sign::Minus {
                        omega = omega.inverse().unwrap();
                    }

                    self.poly.evaluate(&(omega * challenge))
                }
            },
        }
    }
}

impl<F: PrimeField, PC: HomomorphicCommitment<F>> LinearisationQueriable<F, PC>
    for ProverConcreteOracle<F>
{
    fn query_for_linearisation(
        &self,
        rotation: &Rotation,
        context: &LinearisationQueryContext,
        info: &LinearisationInfo<F>,
    ) -> LinearisationQueryResponse<F, PC> {
        match context {
            LinearisationQueryContext::AsEval => {
                if rotation.degree == 0 {
                    let eval = self.poly.evaluate(&info.opening_challenge);
                    return LinearisationQueryResponse::Opening(eval);
                }

                let domain =
                    GeneralEvaluationDomain::<F>::new(info.domain_size)
                        .unwrap();

                let mut omega = domain.element(rotation.degree);
                if rotation.sign == Sign::Minus {
                    omega = omega.inverse().unwrap();
                }

                let eval =
                    self.poly.evaluate(&(omega * info.opening_challenge));
                LinearisationQueryResponse::Opening(eval)
            }
            LinearisationQueryContext::AsPoly => {
                if rotation.degree == 0 {
                    return LinearisationQueryResponse::Poly(self.poly.clone());
                }

                let domain =
                    GeneralEvaluationDomain::<F>::new(info.domain_size)
                        .unwrap();

                let mut omega = domain.element(rotation.degree);
                if rotation.sign == Sign::Minus {
                    omega = omega.inverse().unwrap();
                }

                let shifted_poly = shift_dense_poly(&self.poly, &omega);

                LinearisationQueryResponse::Poly(shifted_poly)
            }
        }
    }
}

impl<F: PrimeField> QuerySetProvider<F> for &ProverConcreteOracle<F> {
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
                let domain =
                    GeneralEvaluationDomain::<F>::new(domain_size).unwrap();
                let (omega, point_label) = match &rotation.sign {
                    Sign::Plus => {
                        let omega = domain.element(rotation.degree);
                        let point_label = format!(
                            "omega_{}_{}",
                            rotation.degree, opening_challenge_label
                        );
                        (omega, point_label)
                    }
                    Sign::Minus => {
                        let omega =
                            domain.element(rotation.degree).inverse().unwrap();
                        let point_label = format!(
                            "omega_-{}_{}",
                            rotation.degree, opening_challenge_label
                        );
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

pub struct VerifierConcreteOracle<
    'a,
    F: PrimeField,
    PC: PolynomialCommitment<F, DensePolynomial<F>>,
> {
    pub(crate) label: String,
    pub(crate) queried_rotations: BTreeSet<Rotation>,
    pub(crate) should_mask: bool,
    pub(crate) eval_at_rotation: BTreeMap<F, Rotation>,
    pub(crate) evals_at_challenges: BTreeMap<F, F>,
    pub(crate) commitment: Option<&'a PC::Commitment>,
}

impl<'a, F: PrimeField, PC: PolynomialCommitment<F, DensePolynomial<F>>> Clone
    for VerifierConcreteOracle<'a, F, PC>
{
    fn clone(&self) -> Self {
        Self {
            label: self.label.clone(),
            queried_rotations: self.queried_rotations.clone(),
            should_mask: self.should_mask.clone(),
            eval_at_rotation: self.eval_at_rotation.clone(),
            evals_at_challenges: self.evals_at_challenges.clone(),
            commitment: self.commitment.clone(),
        }
    }
}

impl<'a, F: PrimeField, PC: PolynomialCommitment<F, DensePolynomial<F>>>
    VerifierConcreteOracle<'a, F, PC>
{
    pub fn new(label: String, should_mask: bool) -> Self {
        Self {
            label,
            should_mask,
            queried_rotations: BTreeSet::new(),
            eval_at_rotation: BTreeMap::new(),
            evals_at_challenges: BTreeMap::new(),
            commitment: None,
        }
    }

    pub fn register_commitment(&mut self, c: &'a PC::Commitment) {
        self.commitment = Some(c)
    }

    pub fn register_rotation(&mut self, rotation: Rotation) {
        self.queried_rotations.insert(rotation);
    }

    // TODO: probably remove
    pub fn register_eval_at_rotation(&mut self, eval: F, rotation: Rotation) {
        let prev_rotation = self.eval_at_rotation.insert(eval, rotation);
        if !prev_rotation.is_none() {
            panic!(
                "Same eval already registered for rotation {:?}",
                prev_rotation
            );
        }
    }

    pub fn register_eval_at_challenge(&mut self, challenge: F, eval: F) {
        let prev_eval = self.evals_at_challenges.insert(challenge, eval);
        if !prev_eval.is_none() {
            panic!("Same eval already registered for challenge {}", challenge);
        }
    }

    pub fn get_degree(&self, domain_size: usize) -> usize {
        if self.should_mask {
            domain_size + self.queried_rotations.len()
        } else {
            domain_size - 1
        }
    }
}

impl<'a, F: PrimeField, PC: PolynomialCommitment<F, DensePolynomial<F>>>
    Queriable<F> for VerifierConcreteOracle<'a, F, PC>
{
    fn query(&self, rotation: &Rotation, context: &QueryContext<F>) -> F {
        match context {
            QueryContext::Instantiation(_, _, _) => {
                panic!(
                    "Can't evaluate verifier oracle in instantiation challenge"
                )
            }
            QueryContext::Opening(domain_size, point) => match point {
                QueryPoint::Omega(_) => {
                    panic!("Can't evaluate at row_i in opening context");
                }
                QueryPoint::Challenge(opening_challenge) => {
                    let domain =
                        GeneralEvaluationDomain::<F>::new(*domain_size)
                            .unwrap();

                    let mut omega = domain.element(rotation.degree);
                    if rotation.sign == Sign::Minus {
                        omega = omega.inverse().unwrap();
                    }

                    let challenge = omega * opening_challenge;

                    match self.evals_at_challenges.get(&challenge) {
                        Some(eval) => *eval,
                        None => panic!(
                            "No eval at challenge: {} of oracle {}",
                            challenge, self.label
                        ),
                    }
                }
            },
        }
    }
}

impl<'a, F: PrimeField, PC: HomomorphicCommitment<F>>
    LinearisationQueriable<F, PC> for VerifierConcreteOracle<'a, F, PC>
{
    fn query_for_linearisation(
        &self,
        rotation: &Rotation,
        context: &LinearisationQueryContext,
        info: &LinearisationInfo<F>,
    ) -> LinearisationQueryResponse<F, PC> {
        match context {
            LinearisationQueryContext::AsEval => {
                let domain =
                    GeneralEvaluationDomain::<F>::new(info.domain_size)
                        .unwrap();

                let mut omega = domain.element(rotation.degree);
                if rotation.sign == Sign::Minus {
                    omega = omega.inverse().unwrap();
                }

                let challenge = omega * info.opening_challenge;

                match self.evals_at_challenges.get(&challenge) {
                    Some(eval) => LinearisationQueryResponse::Opening(*eval),
                    None => panic!(
                        "No eval at challenge: {} of oracle {}",
                        challenge, self.label
                    ),
                }
            }
            // TODO: Consider working with reference to commitment
            LinearisationQueryContext::AsPoly => {
                let commitment = self.commitment.expect(&format!(
                    "Commitment missing for committed oracle {}",
                    self.label
                ));
                LinearisationQueryResponse::Commitment(commitment.clone())
            }
        }
    }
}

impl<'a, F: PrimeField, PC: PolynomialCommitment<F, DensePolynomial<F>>>
    QuerySetProvider<F> for &VerifierConcreteOracle<'a, F, PC>
{
    fn get_query_set(
        &self,
        opening_challenge_label: &str,
        opening_challenge: F,
        domain_size: usize,
    ) -> QuerySet<F> {
        let mut query_set = QuerySet::new();

        let domain = GeneralEvaluationDomain::<F>::new(domain_size).unwrap();
        for rotation in &self.queried_rotations {
            if rotation.degree == 0 {
                query_set.insert((
                    self.label.clone(),
                    (opening_challenge_label.into(), opening_challenge),
                ));
            } else {
                let (omega, point_label) = match &rotation.sign {
                    Sign::Plus => {
                        let omega = domain.element(rotation.degree);
                        let point_label = format!(
                            "omega_{}_{}",
                            rotation.degree, opening_challenge_label
                        );
                        (omega, point_label)
                    }
                    Sign::Minus => {
                        let omega =
                            domain.element(rotation.degree).inverse().unwrap();
                        let point_label = format!(
                            "omega_-{}_{}",
                            rotation.degree, opening_challenge_label
                        );
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

pub fn shift_dense_poly<F: Field>(
    p: &DensePolynomial<F>,
    shifting_factor: &F,
) -> DensePolynomial<F> {
    if *shifting_factor == F::one() {
        return p.clone();
    }

    let mut coeffs = p.coeffs().to_vec();
    let mut acc = F::one();
    for i in 0..coeffs.len() {
        coeffs[i] = coeffs[i] * acc;
        acc *= shifting_factor;
    }

    DensePolynomial::from_coefficients_vec(coeffs)
}
