use std::marker::PhantomData;

use crate::error::Error;
use ark_ff::{to_bytes, PrimeField};
use ark_poly::{univariate::DensePolynomial, EvaluationDomain, GeneralEvaluationDomain};
use ark_poly_commit::PCCommitterKey;
use ark_poly_commit::PolynomialCommitment;
use ark_std::rand::Rng;
use concrete_oracle::{OracleType, ProverConcreteOracle};
use data_structures::ProverKey;
use iop::{prover::ProverState, IOPforPolyIdentity};
use rng::FiatShamirRng;
use vo::VirtualOracle;

pub mod concrete_oracle;
mod data_structures;
pub mod error;
pub mod iop;
pub mod rng;
pub mod vo;

pub struct PIL<F: PrimeField, PC: PolynomialCommitment<F, DensePolynomial<F>>, FS: FiatShamirRng> {
    _field: PhantomData<F>,
    _pc: PhantomData<PC>,
    _fs: PhantomData<FS>,
}

impl<F, PC, FS> PIL<F, PC, FS>
where
    F: PrimeField,
    PC: PolynomialCommitment<F, DensePolynomial<F>>,
    FS: FiatShamirRng,
{
    pub const PROTOCOL_NAME: &'static [u8] = b"PIL-0.0.1";

    // TODO: consider having indexed concrete oracles by initializing evals_at_coset_of_extended_domain (ex. selector polynomials)
    // TODO: consider creating nicer args for this function
    pub fn init_prover<'a>(
        wtns_labels: &[Option<String>],
        wtns_polys: &[DensePolynomial<F>],
        instance_labels: &[Option<String>],
        instance_polys: &[DensePolynomial<F>],
        vos: &'a Vec<Box<dyn VirtualOracle<F>>>,
        domain_size: usize,
        vanishing_polynomial: &DensePolynomial<F>,
    ) -> ProverState<'a, F> {
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
                    should_mask: true, // TODO: keep masking true by default for wtns
                }
            } else {
                ProverConcreteOracle {
                    label: i.to_string(),
                    poly: wtns_poly.clone(),
                    evals_at_coset_of_extended_domain: None,
                    oracle_type: OracleType::Witness,
                    queried_rotations: vec![],
                    should_mask: true, // TODO: keep masking true by default for wtns
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
        }

        let domain = GeneralEvaluationDomain::new(domain_size).unwrap();

        ProverState {
            witness_oracles: witness_oracles.clone(),
            instance_oracles: instance_oracles.clone(),
            vos: vos,
            domain,
            vanishing_polynomial: vanishing_polynomial.clone(),
            quotient_chunks: None,
        }
    }

    pub fn prove<R: Rng>(
        pk: ProverKey<F, PC>,
        wtns_labels: &[Option<String>],
        wtns_polys: &[DensePolynomial<F>],
        instance_labels: &[Option<String>],
        instance_polys: &[DensePolynomial<F>],
        vos: &Vec<Box<dyn VirtualOracle<F>>>,
        domain_size: usize,
        vanishing_polynomial: &DensePolynomial<F>,
        zk_rng: &mut R,
    ) -> Result<(), Error<PC::Error>> {
        let mut prover_state = Self::init_prover(
            wtns_labels,
            wtns_polys,
            instance_labels,
            instance_polys,
            vos,
            domain_size,
            vanishing_polynomial,
        );
        let mut verifier_init_state =
            IOPforPolyIdentity::init_verifier(domain_size, vanishing_polynomial);

        let mut fs_rng = FS::initialize(&to_bytes![&Self::PROTOCOL_NAME].unwrap()); // TODO: add &pk.vk, &public_input to transcript

        // --------------------------------------------------------------------
        // First round

        let prover_first_oracles =
            IOPforPolyIdentity::prover_first_round(&mut prover_state, zk_rng)?;

        let (first_comms, first_comm_rands) =
            PC::commit(&pk.committer_key, prover_first_oracles.iter(), None)
                .map_err(Error::from_pc_err)?;

        fs_rng.absorb(&to_bytes![first_comms].unwrap());

        let (verifier_first_msg, verifier_state) =
            IOPforPolyIdentity::verifier_first_round(verifier_init_state, &mut fs_rng);
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Second round

        let prover_second_oracles = IOPforPolyIdentity::prover_second_round(
            &verifier_first_msg,
            &mut prover_state,
            pk.committer_key.supported_degree(),
        )?;

        let (second_comms, second_comm_rands) =
            PC::commit(&pk.committer_key, prover_second_oracles.iter(), None)
                .map_err(Error::from_pc_err)?;

        fs_rng.absorb(&to_bytes![second_comms].unwrap());

        let (verifier_second_msg, verifier_state) =
            IOPforPolyIdentity::verifier_second_round(verifier_state, &mut fs_rng);
        // --------------------------------------------------------------------

        // Gather prover polynomials in one vector.
        let polynomials: Vec<_> = prover_first_oracles
            .iter()
            .chain(prover_second_oracles.iter())
            .collect();

        let labeled_comms: Vec<_> = first_comms.iter().chain(second_comms.iter()).collect();

        // Gather commitment randomness together.
        let comm_rands: Vec<PC::Randomness> = first_comm_rands
            .into_iter()
            .chain(second_comm_rands)
            .collect();

        // Compute the AHP verifier's query set.
        // let query_set =
        //     IOPforPolyIdentity::get_query_set(&verifier_state);

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        let result = 2 + 2;
        assert_eq!(result, 4);
    }
}
