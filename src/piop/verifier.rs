use crate::{
    commitment::HomomorphicCommitment, oracles::traits::QuerySetProvider,
};
use ark_ff::PrimeField;
use ark_poly_commit::QuerySet;
use ark_std::rand::RngCore;

use super::PIOPforPolyIdentity;

/// State of the verifier
pub struct VerifierState<F: PrimeField> {
    pub(crate) lookup_aggregation_msg:
        Option<VerifierLookupAggregationRound<F>>,
    pub(crate) permutation_msg: Option<VerifierPermutationMsg<F>>,
    pub(crate) first_round_msg: Option<VerifierFirstMsg<F>>,
    pub(crate) second_round_msg: Option<VerifierSecondMsg<F>>,
}

/// Lookup message of the verifier.
#[derive(Copy, Clone)]
pub struct VerifierLookupAggregationRound<F: PrimeField> {
    pub(crate) theta: F,
}

/// Permutation message of the verifier.
#[derive(Copy, Clone)]
pub struct VerifierPermutationMsg<F: PrimeField> {
    pub(crate) beta: F,
    pub(crate) gamma: F,
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

impl<F: PrimeField, PC: HomomorphicCommitment<F>> PIOPforPolyIdentity<F, PC> {
    pub fn init_verifier() -> VerifierState<F> {
        VerifierState {
            lookup_aggregation_msg: None,
            permutation_msg: None,
            first_round_msg: None,
            second_round_msg: None,
        }
    }

    /// Output lookup aggregation challenge
    pub fn verifier_lookup_aggregation_round<R: RngCore>(
        mut state: VerifierState<F>,
        rng: &mut R,
    ) -> (VerifierLookupAggregationRound<F>, VerifierState<F>) {
        let theta = F::rand(rng);

        let msg = VerifierLookupAggregationRound { theta };

        state.lookup_aggregation_msg = Some(msg);
        (msg, state)
    }

    /// Output permutation challenges.
    pub fn verifier_permutation_round<R: RngCore>(
        mut state: VerifierState<F>,
        rng: &mut R,
    ) -> (VerifierPermutationMsg<F>, VerifierState<F>) {
        let beta = F::rand(rng);
        let gamma = F::rand(rng);

        let msg = VerifierPermutationMsg { beta, gamma };

        state.permutation_msg = Some(msg);
        (msg, state)
    }

    // TODO: rename rest of the verifier rounds to more descriptive namings:
    // ex. quotient round, multiopen challenge round, ...

    /// Output the first message.
    pub fn verifier_first_round<R: RngCore>(
        mut state: VerifierState<F>,
        rng: &mut R,
    ) -> (VerifierFirstMsg<F>, VerifierState<F>) {
        let alpha = F::rand(rng);

        let msg = VerifierFirstMsg { alpha };

        state.first_round_msg = Some(msg);
        (msg, state)
    }

    /// Output the second message.
    pub fn verifier_second_round<R: RngCore>(
        mut state: VerifierState<F>,
        rng: &mut R,
    ) -> (VerifierSecondMsg<F>, VerifierState<F>) {
        let xi = F::rand(rng);

        let msg = VerifierSecondMsg { xi, label: "xi" };

        state.second_round_msg = Some(msg);
        (msg, state)
    }

    pub fn get_query_set(
        oracles: &[impl QuerySetProvider<F>],
        evaluation_challenge_label: &str,
        evaluation_challenge: F,
        omegas: &[F],
    ) -> QuerySet<F> {
        let mut query_set = QuerySet::new();

        for oracle in oracles {
            query_set.extend(oracle.get_query_set(
                evaluation_challenge_label,
                evaluation_challenge,
                omegas,
            ));
        }

        query_set
    }
}
