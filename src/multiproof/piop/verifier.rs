use ark_ff::PrimeField;
use ark_std::rand::RngCore;

use super::PIOP;

pub struct VerifierState<F: PrimeField> {
    first_msg: Option<VerifierFirstMsg<F>>,
    second_msg: Option<VerifierSecondMsg<F>>,
    third_msg: Option<VerifierThirdMsg<F>>,
}

/// First message of the verifier.
#[derive(Copy, Clone)]
pub struct VerifierFirstMsg<F: PrimeField> {
    pub(crate) x1: F,
    pub(crate) x2: F,
}

/// Second message of the verifier.
#[derive(Copy, Clone)]
pub struct VerifierSecondMsg<F: PrimeField> {
    pub(crate) x3: F,
}

/// Second message of the verifier.
#[derive(Copy, Clone)]
pub struct VerifierThirdMsg<F: PrimeField> {
    pub(crate) x4: F,
}

impl<F: PrimeField> PIOP<F> {
    pub fn init_verifier() -> VerifierState<F> {
        VerifierState {
            first_msg: None,
            second_msg: None,
            third_msg: None,
        }
    }

    pub fn verifier_first_round<R: RngCore>(
        mut state: VerifierState<F>,
        rng: &mut R,
    ) -> (VerifierState<F>, VerifierFirstMsg<F>) {
        let x1 = F::rand(rng);
        let x2 = F::rand(rng);

        let msg = VerifierFirstMsg { x1, x2 };

        state.first_msg = Some(msg);
        (state, msg)
    }

    pub fn verifier_second_round<R: RngCore>(
        mut state: VerifierState<F>,
        rng: &mut R,
    ) -> (VerifierState<F>, VerifierSecondMsg<F>) {
        let x3 = F::rand(rng);

        let msg = VerifierSecondMsg { x3 };

        state.second_msg = Some(msg);
        (state, msg)
    }

    /// Output the third message.
    pub fn verifier_third_round<R: RngCore>(
        mut state: VerifierState<F>,
        rng: &mut R,
    ) -> (VerifierState<F>, VerifierThirdMsg<F>) {
        let x4 = F::rand(rng);

        let msg = VerifierThirdMsg { x4 };

        state.third_msg = Some(msg);
        (state, msg)
    }
}
