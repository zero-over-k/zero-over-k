use ark_ff::Field;

// use crate::vo::error::Error;
#[derive(PartialEq, PartialOrd, Eq, Ord, Clone, Copy, Debug)]
pub enum Sign {
    Plus,
    Minus,
}

/// Rotation can be positive or negative for an arbitrary degree
#[derive(PartialEq, PartialOrd, Eq, Ord, Clone, Copy, Debug)]
pub struct Rotation {
    pub(crate) degree: usize,
    pub(crate) sign: Sign,
}

impl Rotation {
    pub fn new(degree: usize, sign: Sign) -> Self {
        Self { degree, sign }
    }

    // most common case is to use just curr, next and prev rotations
    pub fn curr() -> Self {
        Self {
            degree: 0,
            sign: Sign::Plus,
        }
    }

    pub fn next() -> Self {
        Self {
            degree: 1,
            sign: Sign::Plus,
        }
    }

    pub fn prev() -> Self {
        Self {
            degree: 1,
            sign: Sign::Minus,
        }
    }

    pub fn compute_evaluation_point<F: Field>(
        &self,
        evaluation_point: F,
        omegas: &Vec<F>,
    ) -> F {
        if self.degree == 0 {
            return evaluation_point;
        }

        let omega = match self.sign {
            Sign::Plus => omegas[self.degree],
            Sign::Minus => omegas[self.degree].inverse().unwrap(),
        };

        evaluation_point * omega
    }

    pub fn get_point_info<F: Field>(
        &self,
        opening_challenge_label: &str,
        opening_challenge: F,
        omegas: &Vec<F>,
    ) -> (String, F) {
        if self.degree == 0 {
            return (opening_challenge_label.into(), opening_challenge);
        } else {
            let (omega, point_label) = match self.sign {
                Sign::Plus => {
                    let omega = omegas[self.degree];
                    let point_label = format!(
                        "omega_{}_{}",
                        self.degree, opening_challenge_label
                    );
                    (omega, point_label)
                }
                Sign::Minus => {
                    let omega = omegas[self.degree].inverse().unwrap();
                    let point_label = format!(
                        "omega_-{}_{}",
                        self.degree, opening_challenge_label
                    );
                    (omega, point_label)
                }
            };

            let point = omega * opening_challenge;
            (point_label, point)
        }
    }
}
