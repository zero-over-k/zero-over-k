use ark_ff::Field;

use crate::concrete_oracle::OracleType;
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

/// Virtual query is defined over relative oracle index that is being resolved
/// for concrete assignment
#[derive(Clone)]
pub struct VirtualQuery {
    pub(crate) index: usize,
    pub(crate) rotation: Rotation,
    pub(crate) oracle_type: OracleType,
}

impl VirtualQuery {
    pub fn new(
        index: usize,
        rotation: Rotation,
        oracle_type: OracleType,
    ) -> Self {
        Self {
            index,
            rotation,
            oracle_type,
        }
    }
}

pub trait Query {
    fn get_type(&self) -> OracleType;
    fn get_index(&self) -> usize;
    fn get_rotation(&self) -> Rotation;
}

/// Witness query is concrete query of an witness oracle given the assignment
#[derive(PartialEq, PartialOrd, Eq, Ord, Clone, Copy)]
pub struct WitnessQuery {
    pub(crate) index: usize,
    pub(crate) rotation: Rotation,
}

impl WitnessQuery {
    pub fn new(index: usize, rotation: Rotation) -> Self {
        Self { index, rotation }
    }
}

impl Query for WitnessQuery {
    fn get_type(&self) -> OracleType {
        OracleType::Witness
    }

    fn get_index(&self) -> usize {
        self.index
    }

    fn get_rotation(&self) -> Rotation {
        self.rotation.clone()
    }
}

/// Instance query is concrete query of an instance oracle given the assignment
#[derive(PartialEq, PartialOrd, Eq, Ord, Clone, Copy)]
pub struct InstanceQuery {
    pub(crate) index: usize,
    pub(crate) rotation: Rotation,
}

impl InstanceQuery {
    pub fn new(index: usize, rotation: Rotation) -> Self {
        Self { index, rotation }
    }
}

impl Query for InstanceQuery {
    fn get_type(&self) -> OracleType {
        OracleType::Instance
    }

    fn get_index(&self) -> usize {
        self.index
    }

    fn get_rotation(&self) -> Rotation {
        self.rotation.clone()
    }
}

#[cfg(test)]
mod test {
    use crate::vo::query::Sign;

    use super::Rotation;

    #[test]
    fn test_no_rotation() {
        let opening_challenge_label = String::from("xi");
        let point_label = String::from("xi");

        let rotation =
            Rotation::from_point_label(&point_label, &opening_challenge_label)
                .unwrap();
        assert_eq!(rotation, Rotation::curr());
    }

    #[test]
    fn test_positive_rotation() {
        let opening_challenge_label = String::from("xi");
        let point_label = String::from("omega_5_xi");

        let rotation =
            Rotation::from_point_label(&point_label, &opening_challenge_label)
                .unwrap();
        assert_eq!(
            rotation,
            Rotation {
                degree: 5,
                sign: Sign::Plus
            }
        );
    }

    #[test]
    fn test_negative_rotation() {
        let opening_challenge_label = String::from("xi");
        let point_label = String::from("omega_-5_xi");

        let rotation =
            Rotation::from_point_label(&point_label, &opening_challenge_label)
                .unwrap();
        assert_eq!(
            rotation,
            Rotation {
                degree: 5,
                sign: Sign::Minus
            }
        );
    }
}

// #[cfg(test)] {
//     mod test {

//     }
// }
