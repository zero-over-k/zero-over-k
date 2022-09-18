use std::marker::PhantomData;

use ark_ff::PrimeField;
use ark_poly::{univariate::DensePolynomial, GeneralEvaluationDomain, EvaluationDomain};
use prover::ProverState;

use crate::{concrete_oracle::{OracleType, ProverConcreteOracle}, vo::VirtualOracle};

pub mod prover;
pub mod verifier;

pub struct IOPforPolyIdentity<F: PrimeField> {
    _field: PhantomData<F>,
}

impl<F: PrimeField> IOPforPolyIdentity<F> {
    pub fn init_prover(
        wtns_labels: &[Option<String>],
        wtns_polys: &[DensePolynomial<F>],
        instance_labels: &[Option<String>],
        instance_polys: &[DensePolynomial<F>],
        vos: &Vec<Box<dyn VirtualOracle<F>>>, 
        domain_size: usize, 
        vanishing_polynomial: &DensePolynomial<F>
    ) {
        // TODO:  compare labels and poly sizes
        let mut witness_oracles = Vec::<ProverConcreteOracle<F>>::with_capacity(wtns_polys.len());
        let mut instance_oracles =
            Vec::<ProverConcreteOracle<F>>::with_capacity(instance_polys.len());

        for (i, (wtns_label, wtns_poly)) in wtns_labels.iter().zip(wtns_polys.iter()).enumerate() {
            let concrete_oracle = if let Some(wtns_label) = wtns_label {
                ProverConcreteOracle {
                    label: wtns_label.into(),
                    poly: wtns_poly.clone(),
                    evals_at_coset_of_extended_domain: None,
                    oracle_type: OracleType::Witness,
                    queried_rotations: vec![],
                    should_mask: true, // TODO: keep masking try by default for wtns
                }
            } else {
                ProverConcreteOracle {
                    label: i.to_string(),
                    poly: wtns_poly.clone(),
                    evals_at_coset_of_extended_domain: None,
                    oracle_type: OracleType::Witness,
                    queried_rotations: vec![],
                    should_mask: true, // TODO: keep masking try by default for wtns
                }
            };

            witness_oracles.push(concrete_oracle);
        }

        for (i, (instance_label, instance_poly)) in instance_labels
            .iter()
            .zip(instance_polys.iter())
            .enumerate()
        {
            let concrete_oracle = if let Some(instance_label) = instance_label {
                ProverConcreteOracle {
                    label: instance_label.into(),
                    poly: instance_poly.clone(),
                    evals_at_coset_of_extended_domain: None,
                    oracle_type: OracleType::Instance,
                    queried_rotations: vec![],
                    should_mask: false,
                }
            } else {
                ProverConcreteOracle {
                    label: i.to_string(),
                    poly: instance_poly.clone(),
                    evals_at_coset_of_extended_domain: None,
                    oracle_type: OracleType::Instance,
                    queried_rotations: vec![],
                    should_mask: false,
                }
            };

            instance_oracles.push(concrete_oracle);

            let domain = GeneralEvaluationDomain::new(domain_size).unwrap();

            ProverState { 
                witness_oracles: witness_oracles.clone(), 
                instance_oracles: instance_oracles.clone(), 
                vos: vos, 
                domain, 
                vanishing_polynomial: vanishing_polynomial.clone(), 
                quotient_chunks: None
            };
        }
    }
}


#[cfg(test)]
mod test {
    use crate::{
        vo::{VirtualOracle, GenericVO, query::{VirtualQuery, Rotation}}, concrete_oracle::OracleType
    };
    use ark_bls12_381::Fr as F;

    #[test]
    fn simple_creation_test() {
        let q1 = VirtualQuery {
            index: 0, 
            rotation: Rotation::curr(), 
            oracle_type: OracleType::Witness
        };

        let q2 = VirtualQuery {
            index: 1, 
            rotation: Rotation::curr(), 
            oracle_type: OracleType::Witness
        };

        // TODO: skip any meaningful checks, plan is to have this implemented 
        // through Expressions similar to halo2

        let mul_vo = GenericVO::new(
            &vec![q1, q2], 
            |wtns_degrees: &Vec<usize>, instance_degrees: &Vec<usize>| {
                wtns_degrees[0] + wtns_degrees[1]
            }, 
            |x: F, wtns_evals: &Vec<F>, instance_evals: &Vec<F>| {
                wtns_evals[0] * instance_evals[1]
            }
        );
    }
}