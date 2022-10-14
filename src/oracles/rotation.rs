

use ark_ff::Field;

use crate::vo::error::Error;
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

    pub fn from_point_label(
        point_label: &String,
        opening_challenge_label: &String,
    ) -> Result<Self, Error> {
        let tokens = point_label.split("_").collect::<Vec<&str>>();

        if tokens.len() == 1 {
            if tokens[0] == opening_challenge_label {
                return Ok(Rotation::curr());
            } else {
                return Err(Error::PointLabelError(point_label.clone()));
            }
        } else if tokens.len() == 3 {
            if tokens[0] != String::from("omega") {
                return Err(Error::PointLabelError(point_label.clone()));
            }
            if tokens[2] != opening_challenge_label {
                return Err(Error::PointLabelError(point_label.clone()));
            }

            let degree = i32::from_str_radix(tokens[1], 10)
                .map_err(Error::from_parse_int_error)?;

            let rotation = if degree > 0 {
                Rotation {
                    degree: degree as usize,
                    sign: Sign::Plus,
                }
            } else {
                Rotation {
                    degree: (-1 * degree) as usize,
                    sign: Sign::Minus,
                }
            };

            return Ok(rotation);
        } else {
            return Err(Error::PointLabelError(point_label.clone()));
        }
    }
}
