use std::{
    cmp::max,
    collections::{BTreeMap, BTreeSet},
    iter::successors,
};

use ark_ff::PrimeField;
use ark_poly::{
    univariate::DensePolynomial, EvaluationDomain, GeneralEvaluationDomain,
    Polynomial, UVPolynomial,
};
use ark_std::rand::Rng;

use crate::{
    commitment::HomomorphicCommitment,
    iop::error::Error,
    iop::{verifier::VerifierFirstMsg, PIOPforPolyIdentity},
    oracles::{
        fixed::FixedOracle,
        instance::InstanceOracle,
        query::{OracleType, QueryContext},
        rotation::Rotation,
        traits::{ConcreteOracle, Instantiable},
        witness::WitnessProverOracle,
    },
    vo::VirtualOracle,
};

// Note: To keep flexible vanishing polynomial should not be strictly domain.vanishing_polynomial
// For example consider https://hackmd.io/1DaroFVfQwySwZPHMoMdBg?view where we remove some roots from Zh

// #[derive(Clone)]
/// State of the prover
pub struct ProverState<'a, F: PrimeField, PC: HomomorphicCommitment<F>> {
    pub(crate) witness_oracles_mapping: BTreeMap<String, usize>, // TODO: introduce &str here maybe
    pub(crate) instance_oracles_mapping: BTreeMap<String, usize>,
    pub(crate) fixed_oracles_mapping: BTreeMap<String, usize>,
    pub(crate) witness_oracles: &'a mut [WitnessProverOracle<F>],
    pub(crate) instance_oracles: &'a mut [InstanceOracle<F>],
    pub(crate) fixed_oracles: &'a mut [FixedOracle<F, PC>],
    pub(crate) vos: &'a [Box<&'a dyn VirtualOracle<F>>],
    pub(crate) domain: GeneralEvaluationDomain<F>,
    pub(crate) vanishing_polynomial: DensePolynomial<F>,
    pub(crate) quotient_chunks: Option<Vec<WitnessProverOracle<F>>>,
}

impl<F: PrimeField, PC: HomomorphicCommitment<F>> PIOPforPolyIdentity<F, PC> {
    // NOTE: consider having indexed concrete oracles by initializing evals_at_coset_of_extended_domain (ex. selector polynomials)
    pub fn init_prover<'a>(
        witness_oracles: &'a mut [WitnessProverOracle<F>],
        instance_oracles: &'a mut [InstanceOracle<F>],
        fixed_oracles: &'a mut [FixedOracle<F, PC>],
        vos: &'a [Box<&'a dyn VirtualOracle<F>>],
        domain_size: usize,
        vanishing_polynomial: &DensePolynomial<F>,
    ) -> ProverState<'a, F, PC> {
        let domain = GeneralEvaluationDomain::new(domain_size).unwrap();

        let witness_oracles_mapping = witness_oracles
            .iter()
            .enumerate()
            .map(|(i, oracle)| (oracle.get_label(), i))
            .collect();
        let instance_oracles_mapping = instance_oracles
            .iter()
            .enumerate()
            .map(|(i, oracle)| (oracle.get_label(), i))
            .collect();
        let fixed_oracles_mapping = fixed_oracles
            .iter()
            .enumerate()
            .map(|(i, oracle)| (oracle.get_label(), i))
            .collect();

        ProverState {
            witness_oracles_mapping,
            instance_oracles_mapping,
            fixed_oracles_mapping,
            witness_oracles,
            instance_oracles,
            fixed_oracles,
            vos,
            domain,
            vanishing_polynomial: vanishing_polynomial.clone(),
            quotient_chunks: None,
        }
    }
    pub fn prover_first_round<'a, R: Rng>(
        state: &'a mut ProverState<F, PC>,
        rng: &mut R,
    ) -> Result<Vec<WitnessProverOracle<F>>, Error> {
        // 1. Get all different witness queries
        for vo in state.vos {
            for query in vo.get_queries() {
                match query.oracle_type {
                    OracleType::Witness => {
                        match state.witness_oracles_mapping.get(&query.label) {
                            Some(index) => state.witness_oracles[*index]
                                .register_rotation(query.rotation),
                            None => panic!(
                                "Witness oracle with label add_label not found"
                            ), //TODO: Introduce new Error here,
                        }
                    }
                    OracleType::Instance => {
                        match state.instance_oracles_mapping.get(&query.label) {
                            Some(index) => state.instance_oracles[*index].register_rotation(query.rotation),
                            None => panic!("Instance oracle with label add_label not found") //TODO: Introduce new Error here,
                        }
                    }
                    OracleType::Fixed => {
                        match state.fixed_oracles_mapping.get(&query.label) {
                            Some(index) => state.fixed_oracles[*index]
                                .register_rotation(query.rotation),
                            None => panic!(
                                "Fixed oracle with label add_label not found"
                            ), //TODO: Introduce new Error here,
                        }
                    }
                }
            }
        }

        // 3. Mask wtns oracles
        for oracle in state.witness_oracles.iter_mut() {
            oracle.mask(&state.vanishing_polynomial, rng);
        }

        Ok(state.witness_oracles.to_vec())
    }

    pub fn prover_second_round(
        verifier_msg: &VerifierFirstMsg<F>,
        state: &mut ProverState<F, PC>,
        _srs_size: usize,
    ) -> Result<Vec<WitnessProverOracle<F>>, Error> {
        // 1. compute quotient degree
        let domain_size = state.domain.size();
        let mut max_degree = 0;
        for vo in state.vos {
            let vo_degree = vo.get_expression().degree(&|query| {
                match query.oracle_type {
                    OracleType::Witness => {
                        match state.witness_oracles_mapping.get(&query.label) {
                            Some(index) => state.witness_oracles[*index]
                                .get_degree(domain_size),
                            None => panic!(
                                "Witness oracle with label add_label not found"
                            ), //TODO: Introduce new Error here,
                        }
                    }
                    OracleType::Instance => {
                        match state.instance_oracles_mapping.get(&query.label) {
                            Some(index) => state.instance_oracles[*index]
                                .get_degree(domain_size),
                            None => panic!(
                                "Witness oracle with label add_label not found"
                            ), //TODO: Introduce new Error here,
                        }
                    }
                    OracleType::Fixed => {
                        match state.fixed_oracles_mapping.get(&query.label) {
                            Some(index) => state.fixed_oracles[*index]
                                .get_degree(domain_size),
                            None => panic!(
                                "Witness oracle with label add_label not found"
                            ), //TODO: Introduce new Error here,
                        }
                    }
                }
            });
            max_degree = max(max_degree, vo_degree);
        }

        let quotient_degree = max_degree - state.vanishing_polynomial.degree();

        // 2. Compute extended domain
        let extended_domain =
            GeneralEvaluationDomain::new(quotient_degree).unwrap();
        let _scaling_ratio = extended_domain.size() / state.domain.size();

        // 3. Compute extended evals of each oracle
        for oracle in state.witness_oracles.iter_mut() {
            oracle.compute_extended_evals(&extended_domain);
        }

        for oracle in state.instance_oracles.iter_mut() {
            oracle.compute_extended_evals(&extended_domain);
        }

        let powers_of_alpha: Vec<F> = successors(Some(F::one()), |alpha_i| {
            Some(*alpha_i * verifier_msg.alpha)
        })
        .take(state.vos.len())
        .collect();

        let mut numerator_evals = vec![F::zero(); extended_domain.size()];

        for i in 0..extended_domain.size() {
            for (vo_index, vo) in state.vos.iter().enumerate() {
                let vo_evaluation = vo.get_expression().evaluate(
                    &|x: F| x,
                    &|query| {
                        // ctx.replace_rotation(query.rotation);
                        let ctx = QueryContext::<F>::ExtendedCoset(state.domain.size(), query.rotation, i); //Maybe we can handle this in a more elegant way
                        match query.oracle_type {
                            OracleType::Witness => {
                                match state.witness_oracles_mapping.get(&query.label) {
                                    Some(index) => state.witness_oracles[*index].query(&ctx),
                                    None => panic!("Witness oracle with label add_label not found") //TODO: Introduce new Error here,
                                }
                            },
                            OracleType::Instance => {
                                match state.instance_oracles_mapping.get(&query.label) {
                                    Some(index) => state.instance_oracles[*index].query(&ctx),
                                    None => panic!("Witness oracle with label add_label not found") //TODO: Introduce new Error here,
                                }
                            },
                            OracleType::Fixed => {
                                match state.fixed_oracles_mapping.get(&query.label) {
                                    Some(index) => state.fixed_oracles[*index].query(&ctx),
                                    None => panic!("Witness oracle with label add_label not found") //TODO: Introduce new Error here,
                                }
                            },
                        }
                    },
                    &|x: F| -x,
                    &|x: F, y: F| x + y,
                    &|x: F, y: F| x * y,
                    &|x: F, y: F| x * y,
                );

                numerator_evals[i] += powers_of_alpha[vo_index] * vo_evaluation;
            }
        }

        let mut zh_evals =
            extended_domain.coset_fft(&state.vanishing_polynomial);
        ark_ff::batch_inversion(&mut zh_evals);

        let quotient_evals: Vec<_> = numerator_evals
            .iter()
            .zip(zh_evals.iter())
            .map(|(&nom, &denom)| nom * denom)
            .collect();

        let quotient = DensePolynomial::from_coefficients_slice(
            &extended_domain.coset_ifft(&quotient_evals),
        );

        let mut quotient_coeffs = Vec::from(quotient.coeffs());
        let padding_size = extended_domain.size() - quotient_coeffs.len();
        if padding_size > 0 {
            quotient_coeffs.extend(vec![F::zero(); padding_size]);
        }

        let quotient_chunks: Vec<WitnessProverOracle<F>> = quotient_coeffs
            .chunks(state.domain.size())
            .enumerate()
            .map(|(i, chunk)| {
                let poly = DensePolynomial::from_coefficients_slice(chunk);
                WitnessProverOracle {
                    label: format!("quotient_chunk_{}", i).to_string(),
                    poly,
                    evals_at_coset_of_extended_domain: None,
                    queried_rotations: BTreeSet::from([Rotation::curr()]),
                    should_mask: false,
                }
            })
            .collect();

        state.quotient_chunks = Some(quotient_chunks.clone());
        Ok(quotient_chunks)
    }
}

#[cfg(test)]
mod test {
    use crate::commitment::{HomomorphicCommitment, KZG10};
    use ark_bls12_381::{Bls12_381, Fr as F};
    use ark_ff::{One, UniformRand};
    use ark_poly::{univariate::DensePolynomial, Polynomial, UVPolynomial};
    use ark_poly_commit::{
        LabeledCommitment, LabeledPolynomial, PCUniversalParams,
        PolynomialCommitment,
    };
    use ark_std::test_rng;

    type PC = KZG10<Bls12_381>;

    #[test]
    fn test_rands_homomorphism() {
        let max_degree = 17;
        let mut rng = test_rng();

        let poly_degree = 10;
        let srs = PC::setup(max_degree, None, &mut rng).unwrap();

        let (committer_key, verifier_key) =
            PC::trim(&srs, srs.max_degree(), 1, None).unwrap();

        let p = DensePolynomial::<F>::rand(poly_degree, &mut rng);
        let p =
            LabeledPolynomial::new("p".to_string(), p.clone(), None, Some(1));
        let q = DensePolynomial::<F>::rand(poly_degree, &mut rng);
        let q =
            LabeledPolynomial::new("q".to_string(), q.clone(), None, Some(1));

        let polys = [p.clone(), q.clone()];

        let (comms, rands) =
            PC::commit(&committer_key, polys.iter(), Some(&mut rng)).unwrap();

        let challenge = F::rand(&mut rng);
        let x1 = F::rand(&mut rng);

        let r = p.polynomial().clone() + q.polynomial() * x1;
        let value = r.evaluate(&challenge);

        let r =
            LabeledPolynomial::new("r".to_string(), r.clone(), None, Some(1));

        let r_comm = PC::add(
            comms[0].commitment(),
            &PC::scale_com(comms[1].commitment(), x1),
        );
        let r_comm =
            LabeledCommitment::new("r_comm".to_string(), r_comm.clone(), None);
        let r_rand = PC::add_rands(&rands[0], &PC::scale_rand(&rands[1], x1));

        // let r_rand = rands[0] + rands[1];

        // let (r_comm, r_rands) = PC::commit(&committer_key, &[r.clone()], Some(&mut rng)).unwrap();
        // println!("r_rand {:?}", r_rands[0]);

        let proof = PC::open(
            &committer_key,
            &[r.clone()],
            &[r_comm],
            &challenge,
            F::one(),
            &[r_rand],
            Some(&mut rng),
        )
        .unwrap();

        // let proof = PC::open(
        //     &committer_key,
        //     polys.iter(),
        //     comms.iter(),
        //     &challenge,
        //     x1,
        //     rands.iter(),
        //     Some(&mut rng)
        // ).unwrap();

        let r_comm = PC::add(
            comms[0].commitment(),
            &PC::scale_com(comms[1].commitment(), x1),
        );
        let r_comm =
            LabeledCommitment::new("r_comm".to_string(), r_comm.clone(), None);

        let res = PC::check(
            &verifier_key,
            &[r_comm.clone()],
            &challenge,
            vec![value],
            &proof,
            F::one(),
            Some(&mut rng),
        )
        .unwrap();
        assert_eq!(res, true);
    }
}
