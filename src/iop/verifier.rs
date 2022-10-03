use crate::{concrete_oracle::QuerySetProvider, iop::error::Error};
use ark_ff::PrimeField;
use ark_poly::{univariate::DensePolynomial, EvaluationDomain, GeneralEvaluationDomain};
use ark_poly_commit::QuerySet;
use ark_std::rand::RngCore;

use super::IOPforPolyIdentity;

/// State of the verifier
pub struct VerifierState<'a, F: PrimeField> {
    pub(crate) domain: GeneralEvaluationDomain<F>,
    pub(crate) vanishing_polynomial: &'a DensePolynomial<F>,

    pub(crate) first_round_msg: Option<VerifierFirstMsg<F>>,
    pub(crate) second_round_msg: Option<VerifierSecondMsg<F>>,
}

/// First message of the verifier.
#[derive(Copy, Clone)]
pub struct VerifierFirstMsg<F: PrimeField> {
    pub(crate) alpha: F,
}

/// Second message of the verifier.
#[derive(Copy, Clone)]
pub struct VerifierSecondMsg<F: PrimeField> {
    pub(crate) xi: F,
    pub(crate) label: &'static str,
}

impl<F: PrimeField> IOPforPolyIdentity<F> {
    pub fn init_verifier(
        domain_size: usize,
        vanishing_polynomial: &DensePolynomial<F>,
    ) -> VerifierState<F> {
        VerifierState {
            domain: GeneralEvaluationDomain::new(domain_size).unwrap(),
            vanishing_polynomial,
            first_round_msg: None,
            second_round_msg: None,
        }
    }
    /// Output the first message.
    pub fn verifier_first_round<'a, R: RngCore>(
        mut state: VerifierState<'a, F>,
        rng: &mut R,
    ) -> (VerifierFirstMsg<F>, VerifierState<'a, F>) {
        let alpha = F::rand(rng);

        let msg = VerifierFirstMsg { alpha };

        state.first_round_msg = Some(msg);
        (msg, state)
    }

    /// Output the second message.
    pub fn verifier_second_round<'a, R: RngCore>(
        mut state: VerifierState<'a, F>,
        rng: &mut R,
    ) -> (VerifierSecondMsg<F>, VerifierState<'a, F>) {
        let xi = F::rand(rng);

        let msg = VerifierSecondMsg { xi, label: "xi" };

        state.second_round_msg = Some(msg);
        (msg, state)
    }

    /// Gets query set for batch poly commit
    pub fn get_query_set<'a>(
        state: &VerifierState<'a, F>,
        queried_oracles: impl Iterator<Item = impl QuerySetProvider<F>>,
    ) -> QuerySet<F> {
        let VerifierSecondMsg { xi, label } = state
            .second_round_msg
            .expect("State should include second round message when building query set");
        let mut query_set = QuerySet::new();

        for queried_oracle in queried_oracles {
            query_set.extend(queried_oracle.get_query_set(label, xi, state.domain.size()));
        }

        query_set
    }
}
