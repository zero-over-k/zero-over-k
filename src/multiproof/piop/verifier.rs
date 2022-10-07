use ark_ff::PrimeField;
use ark_std::rand::RngCore;

use super::PIOP;

pub struct VerifierState<F: PrimeField> {
    evaluation_challenge: F,
    first_msg: Option<VerifierFirstMsg<F>>,
    second_msg: Option<VerifierSecondMsg<F>>,
}

/// First message of the verifier.
#[derive(Copy, Clone)]
pub struct VerifierFirstMsg<F: PrimeField> {
    pub(crate) x1: F,
}

/// Second message of the verifier.
#[derive(Copy, Clone)]
pub struct VerifierSecondMsg<F: PrimeField> {
    pub(crate) x2: F,
    pub(crate) x3: F,
    pub(crate) x4: F,
}

impl<F: PrimeField> PIOP<F> {
    pub fn init_verifier(evaluation_challenge: F) -> VerifierState<F> {
        VerifierState {
            evaluation_challenge,
            first_msg: None,
            second_msg: None,
        }
    }

    pub fn verifier_first_round<R: RngCore>(
        mut state: VerifierState<F>,
        rng: &mut R,
    ) -> (VerifierState<F>, VerifierFirstMsg<F>) {
        let x1 = F::rand(rng);
        let msg = VerifierFirstMsg { x1 };

        state.first_msg = Some(msg);
        (state, msg)
    }

    pub fn verifier_second_round<R: RngCore>(
        mut state: VerifierState<F>,
        rng: &mut R,
    ) -> (VerifierState<F>, VerifierSecondMsg<F>) {
        let x2 = F::rand(rng);
        let x3 = F::rand(rng);
        let x4 = F::rand(rng);

        let msg = VerifierSecondMsg { x2, x3, x4 };

        state.second_msg = Some(msg);
        (state, msg)
    }
}
