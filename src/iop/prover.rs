use std::{cmp::max, collections::BTreeSet, iter::successors};

use ark_ff::PrimeField;
use ark_poly::{
    univariate::DensePolynomial, EvaluationDomain, GeneralEvaluationDomain,
    Polynomial, UVPolynomial,
};
use ark_std::rand::Rng;

use crate::{
    concrete_oracle::{InstantiableConcreteOracle, OracleType},
    iop::error::Error,
    iop::{verifier::VerifierFirstMsg, PIOPforPolyIdentity},
    vo::{
        query::{InstanceQuery, Query, Rotation, WitnessQuery},
        VirtualOracle,
    },
};

// Note: To keep flexible vanishing polynomial should not be strictly domain.vanishing_polynomial
// For example consider https://hackmd.io/1DaroFVfQwySwZPHMoMdBg?view where we remove some roots from Zh

/// State of the prover
pub struct ProverState<'a, F: PrimeField> {
    pub(crate) witness_oracles: Vec<InstantiableConcreteOracle<F>>,
    pub(crate) instance_oracles: Vec<InstantiableConcreteOracle<F>>,
    pub(crate) vos: &'a Vec<Box<dyn VirtualOracle<F>>>,
    pub(crate) domain: GeneralEvaluationDomain<F>,
    pub(crate) vanishing_polynomial: DensePolynomial<F>,
    pub(crate) quotient_chunks: Option<Vec<InstantiableConcreteOracle<F>>>,
}

impl<F: PrimeField> PIOPforPolyIdentity<F> {
    // NOTE: consider having indexed concrete oracles by initializing evals_at_coset_of_extended_domain (ex. selector polynomials)
    pub fn init_prover<'a>(
        concrete_oracles: &[InstantiableConcreteOracle<F>],
        vos: &'a Vec<Box<dyn VirtualOracle<F>>>,
        domain_size: usize,
        vanishing_polynomial: &DensePolynomial<F>,
    ) -> ProverState<'a, F> {
        let mut witness_oracles = vec![];
        let mut instance_oracles = vec![];

        for oracle in concrete_oracles {
            match oracle.oracle_type {
                OracleType::Witness => witness_oracles.push(oracle.clone()),
                OracleType::Instance => instance_oracles.push(oracle.clone()),
            }
        }

        let domain = GeneralEvaluationDomain::new(domain_size).unwrap();

        ProverState {
            witness_oracles: witness_oracles.clone(),
            instance_oracles: instance_oracles.clone(),
            vos,
            domain,
            vanishing_polynomial: vanishing_polynomial.clone(),
            quotient_chunks: None,
        }
    }
    pub fn prover_first_round<'a, R: Rng>(
        state: &'a mut ProverState<F>,
        rng: &mut R,
    ) -> Result<Vec<InstantiableConcreteOracle<F>>, Error> {
        // 1. Get all different witness queries
        let wtns_queries: BTreeSet<WitnessQuery> = state
            .vos
            .iter()
            .map(|vo| vo.get_wtns_queries())
            .flatten()
            .map(|query| query.clone())
            .map(|wtns_query| wtns_query.clone())
            .collect();

        let instance_queries: BTreeSet<InstanceQuery> = state
            .vos
            .iter()
            .map(|vo| vo.get_instance_queries())
            .flatten()
            .map(|query| query.clone())
            .map(|instance_query| instance_query.clone())
            .collect();

        // 2. Assign rotations to matching concrete oracles
        for query in &wtns_queries {
            if query.index >= state.witness_oracles.len() {
                return Err(Error::WtnsQueryIndexOutOfBounds(query.index));
            }

            state.witness_oracles[query.index]
                .register_rotation(query.rotation.clone());
        }

        for query in &instance_queries {
            if query.index >= state.instance_oracles.len() {
                return Err(Error::InstanceQueryIndexOutOfBounds(query.index));
            }

            state.instance_oracles[query.index]
                .register_rotation(query.rotation.clone());
        }

        // 3. Mask wtns oracles
        for oracle in state.witness_oracles.iter_mut() {
            oracle.mask(&state.vanishing_polynomial, rng);
        }

        Ok(state.witness_oracles.clone())
    }

    pub fn prover_second_round(
        verifier_msg: &VerifierFirstMsg<F>,
        state: &mut ProverState<F>,
        srs_size: usize,
    ) -> Result<Vec<InstantiableConcreteOracle<F>>, Error> {
        let wnts_get_degree_fn = |query: &WitnessQuery| {
            let oracle = &state.witness_oracles[query.get_index()];
            oracle.get_degree(state.domain.size())
        };

        let instance_get_degree_fn = |query: &InstanceQuery| {
            let oracle = &state.instance_oracles[query.get_index()];
            oracle.get_degree(state.domain.size())
        };

        // 1. compute quotient degree
        let mut max_degree = 0;
        for vo in state.vos {
            let vo_degree = vo
                .get_expression()
                .degree(&wnts_get_degree_fn, &instance_get_degree_fn);
            max_degree = max(max_degree, vo_degree);
        }

        let quotient_degree = max_degree - state.vanishing_polynomial.degree();

        // 2. Compute extended domain
        let extended_domain =
            GeneralEvaluationDomain::new(quotient_degree).unwrap();
        let _scaling_ratio = extended_domain.size() / state.domain.size();

        // 3. Compute extended evals of each oracle
        for oracle in &mut state.witness_oracles {
            oracle.compute_extended_evals(extended_domain);
        }

        for oracle in &mut state.instance_oracles {
            oracle.compute_extended_evals(extended_domain);
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
                    &|query: &WitnessQuery| {
                        let oracle = &state.witness_oracles[query.get_index()];
                        oracle.query_at_rotated_root_of_extended_domain(
                            state.domain.size(),
                            query.rotation,
                            i,
                        )
                    },
                    &|query: &InstanceQuery| {
                        let oracle = &state.instance_oracles[query.get_index()];
                        oracle.query_at_rotated_root_of_extended_domain(
                            state.domain.size(),
                            query.rotation,
                            i,
                        )
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

        let quotient_chunks: Vec<InstantiableConcreteOracle<F>> =
            quotient_coeffs
                .chunks(state.domain.size())
                .enumerate()
                .map(|(i, chunk)| {
                    let poly = DensePolynomial::from_coefficients_slice(chunk);
                    InstantiableConcreteOracle {
                        label: format!("quotient_chunk_{}", i).to_string(),
                        poly,
                        evals_at_coset_of_extended_domain: None,
                        oracle_type: OracleType::Witness,
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
