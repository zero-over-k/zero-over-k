use super::PrecompiledVO;
use crate::{
    oracles::{query::OracleType, rotation::Rotation},
    vo::{query::VirtualQuery, virtual_expression::VirtualExpression},
};
use ark_ff::PrimeField;

pub struct PrecompiledMul {}

impl<F: PrimeField> PrecompiledVO<F> for PrecompiledMul {
    fn get_expr_and_queries() -> (VirtualExpression<F>, Vec<VirtualQuery>) {
        let q1 = VirtualQuery::new(0, Rotation::curr(), OracleType::Witness);
        let q2 = VirtualQuery::new(1, Rotation::curr(), OracleType::Witness);
        let q3 = VirtualQuery::new(0, Rotation::curr(), OracleType::Instance);

        let mul_expression = {
            let a: VirtualExpression<F> = q1.clone().into();
            let b: VirtualExpression<F> = q2.clone().into();
            let c: VirtualExpression<F> = q3.clone().into();

            a * b - c
        };

        (mul_expression, vec![q1, q2, q3])
    }
}

#[cfg(test)]
mod test {
    use super::PrecompiledMul;
    use std::collections::{BTreeMap, BTreeSet};

    use ark_bls12_381::{Bls12_381, Fr};
    use ark_ff::Zero;
    use ark_poly::Polynomial;
    use ark_poly::{
        univariate::DensePolynomial, EvaluationDomain, GeneralEvaluationDomain,
        UVPolynomial,
    };

    use ark_std::test_rng;
    use rand_chacha::ChaChaRng;

    use crate::data_structures::{
        PermutationInfo, ProverKey, ProverPreprocessedInput,
        VerifierPreprocessedInput,
    };
    use crate::indexer::Indexer;

    use crate::oracles::fixed::{FixedProverOracle, FixedVerifierOracle};
    use crate::oracles::instance::{
        InstanceProverOracle, InstanceVerifierOracle,
    };

    use crate::oracles::witness::{WitnessProverOracle, WitnessVerifierOracle};
    use crate::rng::SimpleHashFiatShamirRng;
    use crate::vo::generic_vo::GenericVO;
    use crate::vo::precompiled::PrecompiledVO;
    use crate::PIL;
    use blake2::Blake2s;

    use crate::commitment::{HomomorphicCommitment, KZG10};
    use crate::vo::VirtualOracle;

    type F = Fr;
    type FS = SimpleHashFiatShamirRng<Blake2s, ChaChaRng>;
    type PC = KZG10<Bls12_381>;

    type PilInstance = PIL<F, PC, FS>;

    #[test]
    fn test_simple_mul() {
        let domain_size = 16;
        let poly_degree = domain_size - 1;
        let max_degree = poly_degree;
        let mut rng = test_rng();

        let srs = PilInstance::universal_setup(max_degree, &mut rng).unwrap();

        let (ck, verifier_key) = PilInstance::prepare_keys(&srs).unwrap();

        let domain = GeneralEvaluationDomain::<F>::new(domain_size).unwrap();

        let a_poly = DensePolynomial::<F>::rand(poly_degree, &mut rng);
        let b_poly = DensePolynomial::<F>::rand(poly_degree, &mut rng);

        let a_evals = domain.fft(&a_poly);
        let b_evals = domain.fft(&b_poly);

        let c_evals = a_evals
            .iter()
            .zip(b_evals.iter())
            .map(|(&a, &b)| a * b)
            .collect::<Vec<_>>();

        let c_poly =
            DensePolynomial::from_coefficients_slice(&domain.ifft(&c_evals));

        for elem in domain.elements() {
            assert_eq!(
                a_poly.evaluate(&elem) * b_poly.evaluate(&elem)
                    - c_poly.evaluate(&elem),
                F::zero()
            );
        }

        let a = WitnessProverOracle::new("a", a_poly, &a_evals, false);
        let b = WitnessProverOracle::new("b", b_poly, &b_evals, false);
        let c = InstanceProverOracle::new("c", c_poly.clone(), &c_evals);

        let mut mul_vo =
            GenericVO::<F>::init(PrecompiledMul::get_expr_and_queries());

        let mut witness_oracles = [a, b];
        let mut instance_oracles = [c];
        let mut fixed_oracles: [FixedProverOracle<F>; 0] = [];

        mul_vo.configure(
            &mut witness_oracles,
            &mut instance_oracles,
            &mut fixed_oracles,
        );

        let vos: Vec<&dyn VirtualOracle<F>> = vec![&mul_vo];

        let vk = Indexer::index(
            &verifier_key,
            &vos,
            vec![],
            &witness_oracles,
            &instance_oracles,
            &fixed_oracles,
            domain,
            &domain.vanishing_polynomial().into(),
            PermutationInfo::dummy(),
            0,
        )
        .unwrap();

        let pk = ProverKey::from_ck_and_vk(&ck, &vk);

        let q_blind = FixedProverOracle {
            label: "q_blind".to_string(),
            poly: DensePolynomial::zero(),
            evals: vec![],
            evals_at_coset_of_extended_domain: None,
            queried_rotations: BTreeSet::default(),
        };

        let preprocessed = ProverPreprocessedInput::new(
            &vec![],
            &vec![],
            &vec![],
            &q_blind,
            &vk.index_info,
        );

        let proof = PilInstance::prove(
            &pk,
            &preprocessed,
            &mut witness_oracles,
            &mut instance_oracles,
            &vos,
            domain_size,
            &domain.vanishing_polynomial().into(),
            &mut rng,
        )
        .unwrap();

        // println!("{}", proof.info());
        // println!("{}", proof.cumulative_info());

        // Verifier
        // Repeat just to make sure some change from prover does not affect this
        let a_ver = WitnessVerifierOracle::<F, PC>::new("a", false);
        let b_ver = WitnessVerifierOracle::<F, PC>::new("b", false);
        let c = InstanceVerifierOracle::new("c", c_poly.clone(), &c_evals);

        let mut ver_wtns_oracles = [a_ver, b_ver];
        let mut instance_oracles = [c];
        let mut fixed_oracles: [FixedVerifierOracle<F, PC>; 0] = [];

        let mut mul_vo =
            GenericVO::<F>::init(PrecompiledMul::get_expr_and_queries());

        mul_vo.configure(
            &mut ver_wtns_oracles,
            &mut instance_oracles,
            &mut fixed_oracles,
        );

        let vos: Vec<&dyn VirtualOracle<F>> = vec![&mul_vo];

        // Repeat but this time provide verifier witness oracles
        let mut vk = Indexer::index(
            &verifier_key,
            &vos,
            vec![],
            &mut ver_wtns_oracles,
            &instance_oracles,
            &fixed_oracles,
            domain,
            &domain.vanishing_polynomial().into(),
            PermutationInfo::dummy(),
            0,
        )
        .unwrap();

        let q_blind = FixedVerifierOracle {
            label: "q_blind".to_string(),
            queried_rotations: BTreeSet::default(),
            evals_at_challenges: BTreeMap::default(),
            commitment: Some(PC::zero_comm()),
        };

        let preprocessed = VerifierPreprocessedInput {
            fixed_oracles: vec![],
            table_oracles: vec![],
            permutation_oracles: vec![],
            q_blind,
        };

        // Since we mutate fixed oracles by adding evals at challenge for specific proof
        // preprocessed input is cloned in order to enable preserving original preprocessed
        // Second option is just to "reset" preprocessed after verification ends
        let mut pp_clone = preprocessed.clone();

        let res = PilInstance::verify(
            &mut vk,
            &mut pp_clone,
            proof,
            &mut ver_wtns_oracles,
            &mut instance_oracles,
            &vos,
            domain_size,
            &domain.vanishing_polynomial().into(),
            &mut rng,
        )
        .unwrap();

        assert_eq!(res, ());
    }
}
