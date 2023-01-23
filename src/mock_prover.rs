use std::marker::PhantomData;

use ark_ff::PrimeField;
use ark_poly::univariate::DensePolynomial;
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};
use ark_poly_commit::PCUniversalParams;
use ark_serialize::{
    CanonicalDeserialize, CanonicalSerialize, SerializationError,
};
use ark_std::io::{Read, Write};

use crate::commitment::HomomorphicCommitment;
use crate::data_structures::{
    ProverKey, ProverPreprocessedInput, UniversalSRS, VerifierKey,
    VerifierPreprocessedInput,
};
use crate::error::Error;
use crate::oracles::instance::{InstanceProverOracle, InstanceVerifierOracle};
use crate::oracles::traits::ConcreteOracle;
use crate::piop::PIOPforPolyIdentity;
use ark_std::rand::{Rng, RngCore};

use crate::oracles::witness::{WitnessProverOracle, WitnessVerifierOracle};
use crate::rng::FiatShamirRng;
use crate::vo::VirtualOracle;

use crate::oracles::query::OracleType;
use crate::{PCKeys, Proof, PIL};

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct MockProof<F, PC>
where
    F: PrimeField,
    PC: HomomorphicCommitment<F>,
{
    _field: PhantomData<F>,
    _pc: PhantomData<PC>,
}

impl<F, PC> MockProof<F, PC>
where
    F: PrimeField,
    PC: HomomorphicCommitment<F>,
{
    fn new() -> Self {
        Self {
            _field: PhantomData::<F>,
            _pc: PhantomData::<PC>,
        }
    }
}

impl<F, PC> Proof for MockProof<F, PC>
where
    F: PrimeField,
    PC: HomomorphicCommitment<F>,
{
    fn info(&self) -> String {
        "This is an empty proof used for the Mock Prover".to_owned()
    }
    fn cumulative_info(&self) -> String {
        self.info()
    }
}

pub struct MockProver<
    F: PrimeField,
    PC: HomomorphicCommitment<F>,
    FS: FiatShamirRng,
> {
    _field: PhantomData<F>,
    _pc: PhantomData<PC>,
    _fs: PhantomData<FS>,
}

impl<F, PC, FS> PIL<F, PC, FS> for MockProver<F, PC, FS>
where
    F: PrimeField,
    PC: HomomorphicCommitment<F>,
    FS: FiatShamirRng,
{
    type Proof = MockProof<F, PC>;
    const PROTOCOL_NAME: &'static [u8] = b"MockProver";

    fn universal_setup<R: RngCore>(
        max_degree: usize,
        rng: &mut R,
    ) -> Result<UniversalSRS<F, PC>, Error<PC::Error>> {
        PC::setup(max_degree, None, rng).map_err(Error::from_pc_err)
    }

    fn prepare_keys(
        srs: &UniversalSRS<F, PC>,
    ) -> Result<PCKeys<F, PC>, Error<PC::Error>> {
        let supported_hiding_bound = 1; // we need to blind oracles for multiproof and opening in x3
        let (committer_key, verifier_key) =
            PC::trim(srs, srs.max_degree(), supported_hiding_bound, None)
                .map_err(Error::from_pc_err)?;

        Ok((committer_key, verifier_key))
    }

    fn prove<'a, R: Rng>(
        _pk: &ProverKey<F, PC>,
        preprocessed: &ProverPreprocessedInput<F, PC>,
        witness_oracles: &'a mut [WitnessProverOracle<F>],
        instance_oracles: &'a mut [InstanceProverOracle<F>],
        vos: &[&'a dyn VirtualOracle<F>], // TODO: this should be in index
        domain_size: usize,
        _zk_rng: &mut R,
    ) -> Result<Self::Proof, Error<PC::Error>> {
        let domain = GeneralEvaluationDomain::new(domain_size).unwrap();
        let omegas: Vec<F> = domain.elements().collect();
        let prover_state = PIOPforPolyIdentity::init_prover(
            witness_oracles,
            instance_oracles,
            vos,
            domain_size,
            preprocessed,
        );
        let evaluate_vo = |vo: &&dyn VirtualOracle<F>, c: F| {
            let vo_evaluation = vo.get_expression().unwrap().evaluate(
                &|x: F| x,
                &|query| {
                    let challenge = query.rotation.compute_evaluation_point(
                        c,
                        &omegas,
                    );
                    match query.oracle_type {
                        OracleType::Witness => {
                            match prover_state.witness_oracles_mapping.get(&query.label) {
                                Some(index) => prover_state.witness_oracles[*index].query(&challenge).unwrap(),
                                None => panic!("Witness oracle with label add_label not found")
                            }
                        },
                        OracleType::Instance => {
                            match prover_state.instance_oracles_mapping.get(&query.label) {
                                Some(index) => prover_state.instance_oracles[*index].query(&challenge).unwrap(),
                                None => panic!("Instance oracle with label {} not found", query.label)
                            }
                        },
                        OracleType::Fixed => {
                            match prover_state.fixed_oracles_mapping.get(&query.label) {
                                Some(index) => preprocessed.fixed_oracles[*index].query(&challenge).unwrap(),
                                None => panic!("Fixed oracle with label add_label not found")
                            }
                        },
                    }
                },
                &|x: F| -x,
                &|x: F, y: F| x + y,
                &|x: F, y: F| x * y,
                &|x: F, y: F| x * y,
            );
            vo_evaluation
        };

        // Check all VOs expressions are 0 in ALL the domain. If some other vanishing poly is being
        // used this check may fail and the proof could still be valid!
        for (row_n, omega) in omegas.iter().enumerate() {
            for (vo_index, vo) in vos.iter().enumerate() {
                let vo_evaluation = evaluate_vo(vo, *omega);

                if vo_evaluation != F::zero() {
                    panic!("VO number {} failed at row {}", vo_index, row_n);
                }
            }
        }

        // TODO: Check permuation argument
        /*
        let coset_deltas = pk.vk.index_info.permutation_argument.deltas;
        for (i, (perm_oracle, w_oracle)) in preprocessed
            .permutation_oracles
            .iter()
            .zip_eq(prover_state.oracles_to_copy.iter())
            .enumerate()
        {
            for (j, (perm_eval, w_eval)) in perm_oracle
                .evals
                .iter()
                .zip_eq(w_oracle.evals.iter())
                .enumerate()
            {
                //TODO: Extract wire_index and row_number from aux structure
                println!(
                    "Checking positions [{}, {}] <=> [{}, {}] \nValues: {:?} {:?} ",
                    i,
                    j,
                    wire_index,
                    row_number,
                    w_eval,
                    &prover_state.oracles_to_copy[wire_index].evals[row_number]
                );
                if *w_eval
                    != prover_state.oracles_to_copy[wire_index].evals
                        [row_number]
                {
                    panic!("Permutation check failed.");
                }
            }
        }
        */

        Ok(MockProof::new())
    }

    #[allow(clippy::too_many_arguments)]
    fn verify(
        _vk: &VerifierKey<F, PC>,
        _preprocessed: &mut VerifierPreprocessedInput<F, PC>,
        _proof: Self::Proof,
        _witness_oracles: &mut [WitnessVerifierOracle<F, PC>],
        _instance_oracles: &mut [InstanceVerifierOracle<F>],
        _vos: &[&dyn VirtualOracle<F>],
        _domain_size: usize,
        _vanishing_polynomial: &DensePolynomial<F>,
    ) -> Result<(), Error<PC::Error>> {
        Ok(())
    }
}
