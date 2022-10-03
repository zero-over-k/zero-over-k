pub mod error;
pub mod prover;
pub mod verifier;

use std::marker::PhantomData;

use ark_ff::{to_bytes, PrimeField};
use ark_poly::{univariate::DensePolynomial, EvaluationDomain, GeneralEvaluationDomain};
use ark_poly_commit::PolynomialCommitment;
use ark_std::rand::Rng;
use prover::ProverState;

use crate::{
    concrete_oracle::{OracleType, ProverConcreteOracle},
    data_structures::ProverKey,
    vo::VirtualOracle,
};

pub struct IOPforPolyIdentity<F: PrimeField> {
    _field: PhantomData<F>,
}

#[cfg(test)]
mod test {
    use crate::{
        concrete_oracle::OracleType,
        vo::{
            query::{Rotation, VirtualQuery},
            VirtualOracle,
        },
    };
    use ark_bls12_381::Fr as F;

    // #[test]
    // fn simple_creation_test() {
    //     let q1 = VirtualQuery {
    //         index: 0,
    //         rotation: Rotation::curr(),
    //         oracle_type: OracleType::Witness
    //     };

    //     let q2 = VirtualQuery {
    //         index: 1,
    //         rotation: Rotation::curr(),
    //         oracle_type: OracleType::Witness
    //     };

    //     // TODO: skip any meaningful checks, plan is to have this implemented
    //     // through Expressions similar to halo2

    //     let mul_vo = GenericVO::new(
    //         &vec![q1, q2],
    //         |wtns_degrees: &Vec<usize>, instance_degrees: &Vec<usize>| {
    //             wtns_degrees[0] + wtns_degrees[1]
    //         },
    //         |x: F, wtns_evals: &Vec<F>, instance_evals: &Vec<F>| {
    //             wtns_evals[0] * instance_evals[1]
    //         }
    //     );
    // }
}
