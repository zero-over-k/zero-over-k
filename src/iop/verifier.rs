use crate::{concrete_oracle::QuerySetProvider, error::Error};
use ark_ff::PrimeField;
use ark_poly::{univariate::DensePolynomial, EvaluationDomain, GeneralEvaluationDomain};
use ark_poly_commit::QuerySet;
use ark_std::rand::RngCore;

use super::IOPforPolyIdentity;

/// State of the verifier
pub struct VerifierState<F: PrimeField> {
    pub(crate) domain: GeneralEvaluationDomain<F>,
    pub(crate) vanishing_polynomial: DensePolynomial<F>,

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
    /// Output the first message.
    pub fn verifier_first_round<R: RngCore>(
        state: &mut VerifierState<F>,
        rng: &mut R,
    ) -> Result<VerifierFirstMsg<F>, Error> {
        let alpha = F::rand(rng);

        let msg = VerifierFirstMsg { alpha };

        state.first_round_msg = Some(msg);
        Ok(msg)
    }

    /// Output the second message.
    pub fn verifier_second_round<R: RngCore>(
        state: &mut VerifierState<F>,
        rng: &mut R,
    ) -> Result<VerifierSecondMsg<F>, Error> {
        let xi = F::rand(rng);

        let msg = VerifierSecondMsg { xi, label: "xi" };

        state.second_round_msg = Some(msg);
        Ok(msg)
    }

    /// Gets query set for batch poly commit
    pub fn get_query_set(
        state: &VerifierState<F>,
        queried_oracles: &Vec<impl QuerySetProvider<F>>,
    ) {
        let VerifierSecondMsg { xi, label } = state
            .second_round_msg
            .expect("State should include second round message when building query set");
        let mut query_set = QuerySet::new();

        for queried_oracle in queried_oracles {
            query_set.extend(queried_oracle.get_query_set(label, xi, state.domain.size()));
        }
    }
}
