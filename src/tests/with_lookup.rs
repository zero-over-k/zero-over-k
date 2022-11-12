#[cfg(test)]
mod test {
    use std::collections::{BTreeMap, BTreeSet};

    use ark_bls12_381::{Bls12_381, Fr as F};
    use ark_ff::{UniformRand, Zero};
    use ark_poly::{univariate::DensePolynomial, GeneralEvaluationDomain};
    use ark_poly::{EvaluationDomain, UVPolynomial};
    use ark_poly_commit::{LabeledPolynomial, PolynomialCommitment};
    use ark_std::test_rng;
    use rand_chacha::ChaChaRng;

    use crate::commitment::KZG10;
    use crate::data_structures::{
        PermutationInfo, ProverKey, ProverPreprocessedInput,
        VerifierPreprocessedInput,
    };
    use crate::indexer::Indexer;
    use crate::oracles::fixed::{FixedProverOracle, FixedVerifierOracle};
    use crate::oracles::instance::InstanceVerifierOracle;
    use crate::oracles::query::OracleType;
    use crate::oracles::rotation::Rotation;
    use crate::oracles::traits::Instantiable;
    use crate::oracles::witness::WitnessVerifierOracle;
    use crate::oracles::{
        instance::InstanceProverOracle, witness::WitnessProverOracle,
    };
    use crate::rng::SimpleHashFiatShamirRng;
    use crate::vo::generic_lookup_vo::GenericLookupVO;
    use crate::vo::generic_vo::GenericVO;

    use crate::vo::query::VirtualQuery;
    use crate::vo::virtual_expression::VirtualExpression;
    use crate::vo::{LookupVirtualOracle, VirtualOracle};
    use crate::PIL;
    use blake2::Blake2s;

    type FS = SimpleHashFiatShamirRng<Blake2s, ChaChaRng>;
    type PC = KZG10<Bls12_381>;

    type PilInstance = PIL<F, PC, FS>;

    fn get_lookup_expressions_and_queries() -> (
        Vec<VirtualExpression<F>>,
        Vec<VirtualQuery>,
        Vec<VirtualQuery>,
    ) {
        let q1 = VirtualQuery::new(0, Rotation::curr(), OracleType::Witness);
        let t_q1 = VirtualQuery::new(0, Rotation::curr(), OracleType::Fixed);

        let expr1: VirtualExpression<F> = q1.clone().into();

        let expressions = vec![expr1];
        let queries = vec![q1];
        let table_queries = vec![t_q1];

        (expressions, queries, table_queries)
    }

    fn get_vo_expression_and_queries(
    ) -> (VirtualExpression<F>, Vec<VirtualQuery>) {
        let q1 = VirtualQuery::new(0, Rotation::curr(), OracleType::Witness);
        let q2 = VirtualQuery::new(1, Rotation::curr(), OracleType::Witness);
        let q3 = VirtualQuery::new(2, Rotation::curr(), OracleType::Witness);

        let q4 = VirtualQuery::new(0, Rotation::curr(), OracleType::Fixed);

        let mul_expression = {
            let a: VirtualExpression<F> = q1.clone().into();
            let b: VirtualExpression<F> = q2.clone().into();
            let c: VirtualExpression<F> = q3.clone().into();

            let q: VirtualExpression<F> = q4.clone().into();

            q * (a * b - c)
        };

        (mul_expression, vec![q1, q2, q3, q4])
    }

    #[test]
    fn test_full_circuit_simple_lookup() {
        let convert_to_field = |x: &[usize]| -> Vec<F> {
            x.iter().map(|&xi| F::from(xi as u64)).collect()
        };

        let domain_size = 16;
        let poly_degree = domain_size - 1;
        let max_degree = poly_degree;
        let mut rng = test_rng();

        let srs = PilInstance::universal_setup(max_degree, &mut rng).unwrap();

        let (ck, verifier_key) = PilInstance::prepare_keys(&srs).unwrap();

        let domain = GeneralEvaluationDomain::<F>::new(domain_size).unwrap();

        let scaling_factor = 4;

        let extended_coset_domain =
            GeneralEvaluationDomain::<F>::new(scaling_factor * domain_size)
                .unwrap();

        let usable_rows = 10;
        let dummy_table = 999;
        let table_evals = [
            1,
            2,
            3,
            4,
            5,
            6,
            7,
            dummy_table,
            dummy_table,
            dummy_table,
            dummy_table,
            dummy_table,
            dummy_table,
            dummy_table,
            dummy_table,
            dummy_table,
        ];
        let table_evals = convert_to_field(&table_evals);

        let a_evals = [
            1,
            1,
            2,
            3,
            4,
            4,
            dummy_table,
            dummy_table,
            dummy_table,
            dummy_table,
        ];
        let mut a_evals = convert_to_field(&a_evals);

        let b_evals = [
            // actual values but they can be random
            F::rand(&mut rng),
            F::rand(&mut rng),
            F::rand(&mut rng),
            F::rand(&mut rng),
            F::rand(&mut rng),
            F::rand(&mut rng),
            F::rand(&mut rng),
            F::rand(&mut rng),
            F::rand(&mut rng),
            F::rand(&mut rng),
            // now blinds
            F::rand(&mut rng),
            F::rand(&mut rng),
            F::rand(&mut rng),
            F::rand(&mut rng),
            F::rand(&mut rng),
            F::rand(&mut rng),
        ];

        let mut c_evals: Vec<F> = a_evals
            .iter()
            .take(usable_rows)
            .zip(b_evals.iter().take(usable_rows))
            .map(|(&a, &b)| a * b)
            .collect();

        for _ in usable_rows..domain_size {
            c_evals.push(F::rand(&mut rng));
            a_evals.push(F::rand(&mut rng));
        }

        assert_eq!(c_evals.len(), domain_size);

        let selector_evals = [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0];
        let q_blind_evals = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1];

        let selector_evals = convert_to_field(&selector_evals);
        let q_blind_evals = convert_to_field(&q_blind_evals);

        // sanity check
        for i in 0..domain_size {
            assert_eq!(
                F::zero(),
                selector_evals[i] * (a_evals[i] * b_evals[i] - c_evals[i])
            );
        }

        let a_poly =
            DensePolynomial::from_coefficients_slice(&domain.ifft(&a_evals));
        let a = WitnessProverOracle {
            label: "a".to_string(),
            poly: a_poly,
            evals_at_coset_of_extended_domain: None,
            queried_rotations: BTreeSet::new(),
            should_permute: false,
            evals: a_evals,
        };

        let b_poly =
            DensePolynomial::from_coefficients_slice(&domain.ifft(&b_evals));
        let b = WitnessProverOracle {
            label: "b".to_string(),
            poly: b_poly,
            evals_at_coset_of_extended_domain: None,
            queried_rotations: BTreeSet::new(),
            should_permute: false,
            evals: b_evals.to_vec(),
        };

        let c_poly =
            DensePolynomial::from_coefficients_slice(&domain.ifft(&c_evals));
        let c = WitnessProverOracle {
            label: "c".to_string(),
            poly: c_poly,
            evals_at_coset_of_extended_domain: None,
            queried_rotations: BTreeSet::new(),
            should_permute: false,
            evals: c_evals,
        };

        let q_poly = DensePolynomial::from_coefficients_slice(
            &domain.ifft(&selector_evals),
        );
        let q = FixedProverOracle {
            label: "q".to_string(),
            poly: q_poly.clone(),
            evals_at_coset_of_extended_domain: None,
            queried_rotations: BTreeSet::new(),
            evals: selector_evals,
        };

        let q_blind_poly = DensePolynomial::from_coefficients_slice(
            &domain.ifft(&q_blind_evals),
        );

        let q_blind = FixedProverOracle {
            label: "q_blind".to_string(),
            poly: q_blind_poly.clone(),
            evals_at_coset_of_extended_domain: Some(
                extended_coset_domain.coset_fft(&q_blind_poly),
            ),
            evals: q_blind_evals.to_vec(),
            queried_rotations: BTreeSet::from([Rotation::curr()]),
        };

        let table_poly = DensePolynomial::from_coefficients_slice(
            &domain.ifft(&table_evals),
        );
        let t = FixedProverOracle {
            label: "t".to_string(),
            poly: table_poly.clone(),
            evals_at_coset_of_extended_domain: None,
            queried_rotations: BTreeSet::new(),
            evals: table_evals,
        };

        let mut witness_oracles = [a, b, c];
        let mut instance_oracles: [InstanceProverOracle<F>; 0] = [];
        let mut fixed_oracles = [q];
        let mut table_oracles = [t];

        let mut mul_vo = GenericVO::<F>::init(get_vo_expression_and_queries());

        let mut lookup_vo =
            GenericLookupVO::<F>::init(get_lookup_expressions_and_queries());

        mul_vo.configure(
            &mut witness_oracles,
            &mut instance_oracles,
            &mut fixed_oracles,
        );

        lookup_vo.configure(
            &mut witness_oracles,
            &mut instance_oracles,
            &mut fixed_oracles,
            &mut table_oracles,
        );

        let vos: Vec<&dyn VirtualOracle<F>> = vec![&mul_vo];
        let lookups: Vec<&dyn LookupVirtualOracle<F>> = vec![&lookup_vo];

        let vk = Indexer::<F, PC>::index(
            &verifier_key,
            &vos,
            lookups,
            &witness_oracles,
            &instance_oracles,
            &fixed_oracles,
            domain,
            &domain.vanishing_polynomial().into(),
            PermutationInfo::dummy(),
            usable_rows,
        )
        .unwrap();

        let pk = ProverKey::from_ck_and_vk(&ck, &vk);

        let preprocessed = ProverPreprocessedInput::new(
            &fixed_oracles.to_vec(),
            &vec![],
            &table_oracles.to_vec(),
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
        println!("{}", proof.cumulative_info());

        //Verifier
        let a_ver = WitnessVerifierOracle::<F, PC> {
            label: "a".to_string(),
            queried_rotations: BTreeSet::default(),
            should_permute: false,
            evals_at_challenges: BTreeMap::default(),
            commitment: None,
        };

        let b_ver = WitnessVerifierOracle {
            label: "b".to_string(),
            queried_rotations: BTreeSet::default(),
            should_permute: false,
            evals_at_challenges: BTreeMap::default(),
            commitment: None,
        };

        let c_ver = WitnessVerifierOracle {
            label: "c".to_string(),
            queried_rotations: BTreeSet::default(),
            should_permute: false,
            evals_at_challenges: BTreeMap::default(),
            commitment: None,
        };

        let labeled_selectors: Vec<LabeledPolynomial<F, DensePolynomial<F>>> =
            [(q_poly.clone(), "q")]
                .iter()
                .map(|(poly, label)| {
                    LabeledPolynomial::new(
                        label.to_string(),
                        poly.clone(),
                        None,
                        None,
                    )
                })
                .collect();

        let (selector_commitments, _) =
            PC::commit(&ck, labeled_selectors.iter(), None).unwrap();

        let mut fixed_oracles: Vec<_> = selector_commitments
            .iter()
            .map(|cmt| FixedVerifierOracle::<F, PC> {
                label: cmt.label().clone(),
                queried_rotations: BTreeSet::default(),
                evals_at_challenges: BTreeMap::default(),
                commitment: Some(cmt.commitment().clone()),
            })
            .collect();

        let labeled_table_oracles: Vec<
            LabeledPolynomial<F, DensePolynomial<F>>,
        > = [(table_poly.clone(), "t")]
            .iter()
            .map(|(poly, label)| {
                LabeledPolynomial::new(
                    label.to_string(),
                    poly.clone(),
                    None,
                    None,
                )
            })
            .collect();

        let (table_commitments, _) =
            PC::commit(&ck, labeled_table_oracles.iter(), None).unwrap();

        let mut table_oracles: Vec<_> = table_commitments
            .iter()
            .map(|cmt| FixedVerifierOracle::<F, PC> {
                label: cmt.label().clone(),
                queried_rotations: BTreeSet::default(),
                evals_at_challenges: BTreeMap::default(),
                commitment: Some(cmt.commitment().clone()),
            })
            .collect();

        let q_blind_labeled = q_blind.to_labeled();
        let (q_blind_commitment, _) =
            PC::commit(&ck, &[q_blind_labeled], None).unwrap();

        let q_blind = FixedVerifierOracle::<F, PC> {
            label: "q_blind".into(),
            queried_rotations: BTreeSet::from([Rotation::curr()]),
            evals_at_challenges: BTreeMap::default(),
            commitment: Some(q_blind_commitment[0].commitment().clone()),
        };

        let mut ver_wtns_oracles = [a_ver, b_ver, c_ver];
        let mut instance_oracles: [InstanceVerifierOracle<F>; 0] = [];

        let mut mul_vo = GenericVO::<F>::init(get_vo_expression_and_queries());

        let mut lookup_vo =
            GenericLookupVO::<F>::init(get_lookup_expressions_and_queries());

        mul_vo.configure(
            &mut ver_wtns_oracles,
            &mut instance_oracles,
            &mut fixed_oracles,
        );

        lookup_vo.configure(
            &mut ver_wtns_oracles,
            &mut instance_oracles,
            &mut fixed_oracles,
            &mut table_oracles,
        );

        let vos: Vec<&dyn VirtualOracle<F>> = vec![&mul_vo];
        let lookups: Vec<&dyn LookupVirtualOracle<F>> = vec![&lookup_vo];

        let mut vk = Indexer::<F, PC>::index(
            &verifier_key,
            &vos,
            lookups,
            &mut ver_wtns_oracles,
            &instance_oracles,
            &fixed_oracles,
            domain,
            &domain.vanishing_polynomial().into(),
            PermutationInfo::dummy(),
            0,
        )
        .unwrap();

        let preprocessed = VerifierPreprocessedInput {
            fixed_oracles: fixed_oracles,
            table_oracles: table_oracles,
            permutation_oracles: vec![],
            q_blind: q_blind,
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
