use crate::{
    oracles::{query::OracleType, rotation::Rotation},
    vo::{query::VirtualQuery, virtual_expression::VirtualExpression},
};
use ark_ff::PrimeField;

use super::PrecompiledVO;

/// Plonk's original arithmetic constraint:
/// q_m * a * b + q_L * a + q_R * b + q_o * c + q_c + PI = 0
pub struct PrecompiledPlonkArith {}

impl<F: PrimeField> PrecompiledVO<F> for PrecompiledPlonkArith {
    fn get_expr_and_queries() -> (VirtualExpression<F>, Vec<VirtualQuery>) {
        // Selectors
        let qm = VirtualQuery::new(0, Rotation::curr(), OracleType::Fixed);
        let ql = VirtualQuery::new(1, Rotation::curr(), OracleType::Fixed);
        let qr = VirtualQuery::new(2, Rotation::curr(), OracleType::Fixed);
        let qo = VirtualQuery::new(3, Rotation::curr(), OracleType::Fixed);
        let qc = VirtualQuery::new(4, Rotation::curr(), OracleType::Fixed);

        // Pub input
        let pi = VirtualQuery::new(0, Rotation::curr(), OracleType::Instance);

        // Witnesses
        let a = VirtualQuery::new(0, Rotation::curr(), OracleType::Witness);
        let b = VirtualQuery::new(1, Rotation::curr(), OracleType::Witness);
        let c = VirtualQuery::new(2, Rotation::curr(), OracleType::Witness);

        let plonk_expression = {
            let qm: VirtualExpression<F> = qm.clone().into();
            let ql: VirtualExpression<F> = ql.clone().into();
            let qr: VirtualExpression<F> = qr.clone().into();
            let qo: VirtualExpression<F> = qo.clone().into();
            let qc: VirtualExpression<F> = qc.clone().into();

            let pi: VirtualExpression<F> = pi.clone().into();

            let a: VirtualExpression<F> = a.clone().into();
            let b: VirtualExpression<F> = b.clone().into();
            let c: VirtualExpression<F> = c.clone().into();

            a.clone() * b.clone() * qm + a * ql + b * qr + c * qo + qc + pi
        };

        (plonk_expression, vec![qm, ql, qr, qo, qc, pi, a, b, c])
    }
}

/// Plonk's orginal arithmetic constraint with an extra addend using 4 wires.
/// q_m * a * b + q_L * a + q_R * b + q_o * c + q_4 * d + q_c + PI = 0
pub struct PlonkArith4 {}

impl<F: PrimeField> PrecompiledVO<F> for PlonkArith4 {
    fn get_expr_and_queries() -> (VirtualExpression<F>, Vec<VirtualQuery>) {
        // Selectors
        let qm = VirtualQuery::new(0, Rotation::curr(), OracleType::Fixed);
        let ql = VirtualQuery::new(1, Rotation::curr(), OracleType::Fixed);
        let qr = VirtualQuery::new(2, Rotation::curr(), OracleType::Fixed);
        let q4 = VirtualQuery::new(3, Rotation::curr(), OracleType::Fixed);
        let qo = VirtualQuery::new(4, Rotation::curr(), OracleType::Fixed);
        let qc = VirtualQuery::new(5, Rotation::curr(), OracleType::Fixed);

        // Pub input
        let pi = VirtualQuery::new(0, Rotation::curr(), OracleType::Instance);

        // Witnesses
        let a = VirtualQuery::new(0, Rotation::curr(), OracleType::Witness);
        let b = VirtualQuery::new(1, Rotation::curr(), OracleType::Witness);
        let c = VirtualQuery::new(2, Rotation::curr(), OracleType::Witness);
        let d = VirtualQuery::new(2, Rotation::curr(), OracleType::Witness);

        let plonk_expression = {
            let qm: VirtualExpression<F> = qm.clone().into();
            let ql: VirtualExpression<F> = ql.clone().into();
            let qr: VirtualExpression<F> = qr.clone().into();
            let q4: VirtualExpression<F> = q4.clone().into();
            let qo: VirtualExpression<F> = qo.clone().into();
            let qc: VirtualExpression<F> = qc.clone().into();

            let pi: VirtualExpression<F> = pi.clone().into();

            let a: VirtualExpression<F> = a.clone().into();
            let b: VirtualExpression<F> = b.clone().into();
            let c: VirtualExpression<F> = c.clone().into();
            let d: VirtualExpression<F> = d.clone().into();

            a.clone() * b.clone() * qm
                + a * ql
                + b * qr
                + d * q4
                + c * qo
                + pi
                + qc
        };

        (plonk_expression, vec![qm, ql, qr, q4, qo, qc, pi, a, b, c])
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use std::collections::{BTreeMap, BTreeSet};

    use ark_bls12_381::{Bls12_381, Fr};
    use ark_ff::{One, UniformRand, Zero};
    use ark_poly::Polynomial;
    use ark_poly::{
        univariate::DensePolynomial, EvaluationDomain, GeneralEvaluationDomain,
        UVPolynomial,
    };

    use ark_poly_commit::{LabeledPolynomial, PolynomialCommitment};

    use ark_std::test_rng;
    use rand_chacha::ChaChaRng;

    use crate::data_structures::{
        ProverKey, ProverPreprocessedInput, VerifierPreprocessedInput,
    };
    use crate::indexer::Indexer;

    use crate::oracles::fixed::{FixedProverOracle, FixedVerifierOracle};
    use crate::oracles::instance::{
        InstanceProverOracle, InstanceVerifierOracle,
    };

    use crate::oracles::witness::{WitnessProverOracle, WitnessVerifierOracle};
    use crate::rng::SimpleHashFiatShamirRng;
    use crate::vo::generic_vo::GenericVO;
    use crate::vo::VirtualOracle;
    use crate::PIL;
    use blake2::Blake2s;

    use crate::commitment::KZG10;

    type F = Fr;
    type FS = SimpleHashFiatShamirRng<Blake2s, ChaChaRng>;
    type PC = KZG10<Bls12_381>;

    type PilInstance = PIL<F, PC, FS>;

    #[test]
    fn test_plonk_arith() {
        let domain_size = 4;
        let poly_degree = domain_size - 1;
        let max_degree = poly_degree;
        let mut rng = test_rng();

        let srs = PilInstance::universal_setup(max_degree, &mut rng).unwrap();

        let (ck, verifier_key) = PilInstance::prepare_keys(&srs).unwrap();

        let domain = GeneralEvaluationDomain::<F>::new(domain_size).unwrap();

        /*
            a <- rand
            b <- rand
            pi <- rand

            c[0] = a * b
            c[1] = a + b
            c[2] = pi[2]
            c[3] = a * b

            rows:
                0 qm = 1, ql = 0, qr = 0, qo = -1, qpi = 0
                1 qm = 0, ql = 1, qr = 1, qo = -1, qpi = 0
                2 qm = 0, ql = 0, qr = 0, qo = 1, qpi = -pi[2]
                3 qm = 1, ql = 0, qr = 0, qo = -1, qpi = 0
        */

        let a_poly = DensePolynomial::<F>::rand(poly_degree, &mut rng);
        let b_poly = DensePolynomial::<F>::rand(poly_degree, &mut rng);

        let a_evals = domain.fft(&a_poly);
        let b_evals = domain.fft(&b_poly);

        let mut c_evals = vec![F::zero(); domain_size];

        let mut pi_evals = vec![F::zero(); domain_size];
        pi_evals[2] = F::rand(&mut rng);

        let mut qm_evals = vec![F::zero(); domain_size];
        let mut ql_evals = vec![F::zero(); domain_size];
        let mut qr_evals = vec![F::zero(); domain_size];
        let mut qo_evals = vec![F::zero(); domain_size];
        let mut qpi_evals = vec![F::zero(); domain_size];

        // row0
        c_evals[0] = a_evals[0] * b_evals[0];
        qm_evals[0] = F::one();
        qo_evals[0] = -F::one();

        // row1
        c_evals[1] = a_evals[1] + b_evals[1];
        ql_evals[1] = F::one();
        qr_evals[1] = F::one();
        qo_evals[1] = -F::one();

        //row2
        c_evals[2] = pi_evals[2];
        qpi_evals[2] = -pi_evals[2];

        //row3
        c_evals[3] = a_evals[3] * b_evals[3];
        qm_evals[3] = F::one();
        qo_evals[3] = -F::one();

        // Define oracles
        let c_poly =
            DensePolynomial::from_coefficients_slice(&domain.ifft(&c_evals));
        let pi_poly =
            DensePolynomial::from_coefficients_slice(&domain.ifft(&pi_evals));

        let qm_poly =
            DensePolynomial::from_coefficients_slice(&domain.ifft(&qm_evals));
        let ql_poly =
            DensePolynomial::from_coefficients_slice(&domain.ifft(&ql_evals));
        let qr_poly =
            DensePolynomial::from_coefficients_slice(&domain.ifft(&qr_evals));
        let qo_poly =
            DensePolynomial::from_coefficients_slice(&domain.ifft(&qo_evals));
        let qpi_poly =
            DensePolynomial::from_coefficients_slice(&domain.ifft(&qpi_evals));

        for (_i, elem) in domain.elements().enumerate() {
            let a = a_poly.evaluate(&elem);
            let b = b_poly.evaluate(&elem);
            let c = c_poly.evaluate(&elem);

            let pi = pi_poly.evaluate(&elem);

            let qm = qm_poly.evaluate(&elem);
            let ql = ql_poly.evaluate(&elem);
            let qr = qr_poly.evaluate(&elem);
            let qo = qo_poly.evaluate(&elem);
            let qpi = qpi_poly.evaluate(&elem);

            let plonk_arith = a * b * qm + a * ql + b * qr + c * qo + pi + qpi;
            assert_eq!(plonk_arith, F::zero());
        }

        let a = WitnessProverOracle {
            label: "a".to_string(),
            poly: a_poly,
            evals_at_coset_of_extended_domain: None,
            queried_rotations: BTreeSet::new(),
            should_permute: false,
            evals: a_evals.clone(),
        };

        let b = WitnessProverOracle {
            label: "b".to_string(),
            poly: b_poly,
            evals_at_coset_of_extended_domain: None,
            queried_rotations: BTreeSet::new(),
            should_permute: false,
            evals: b_evals.clone(),
        };

        let c = WitnessProverOracle {
            label: "c".to_string(),
            poly: c_poly,
            evals_at_coset_of_extended_domain: None,
            queried_rotations: BTreeSet::new(),
            should_permute: false,
            evals: c_evals.clone(),
        };

        let pi = InstanceProverOracle {
            label: "pi".to_string(),
            poly: pi_poly.clone(),
            evals_at_coset_of_extended_domain: None,
            queried_rotations: BTreeSet::new(),
            evals: pi_evals.clone(),
        };

        let mut witness_oracles = [a, b, c];
        let mut instance_oracles = [pi];

        let mut selector_oracles: Vec<_> = [
            (qm_poly.clone(), "qm"),
            (ql_poly.clone(), "ql"),
            (qr_poly.clone(), "qr"),
            (qo_poly.clone(), "qo"),
            (qpi_poly.clone(), "qpi"),
        ]
        .into_iter()
        .map(|(poly, label)| FixedProverOracle::<F> {
            label: label.to_string(),
            evals: domain.fft(&poly),
            poly,
            evals_at_coset_of_extended_domain: None,
            queried_rotations: BTreeSet::new(),
        })
        .collect();

        let mut plonk_vo = GenericVO::<F, PC>::init(
            PrecompiledPlonkArith::get_expr_and_queries(),
        );

        plonk_vo.configure(
            &mut witness_oracles,
            &mut instance_oracles,
            &mut selector_oracles,
        );

        let vos: Vec<&dyn VirtualOracle<F>> = vec![&plonk_vo];

        let vk = Indexer::index(
            &verifier_key,
            &vos,
            &witness_oracles,
            &instance_oracles,
            &selector_oracles,
            domain,
            &domain.vanishing_polynomial().into(),
            None,
        )
        .unwrap();

        let pk = ProverKey::from_ck_and_vk(&ck, &vk);

        let preprocessed = ProverPreprocessedInput::new(
            &selector_oracles,
            &vec![],
            None,
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

        // Verifier

        let mut witness_ver_oracles: Vec<_> = ["a", "b", "c"]
            .into_iter()
            .map(|label| WitnessVerifierOracle {
                label: label.to_string(),
                queried_rotations: BTreeSet::new(),
                should_permute: false,
                evals_at_challenges: BTreeMap::default(),
                commitment: None,
            })
            .collect();

        let pi = InstanceVerifierOracle {
            label: "pi".to_string(),
            poly: pi_poly.clone(),
            evals: pi_evals.clone(),
            queried_rotations: BTreeSet::new(),
        };

        let mut instance_oracles = [pi];

        let labeled_selectors: Vec<LabeledPolynomial<F, DensePolynomial<F>>> =
            [
                (qm_poly.clone(), "qm"),
                (ql_poly.clone(), "ql"),
                (qr_poly.clone(), "qr"),
                (qo_poly.clone(), "qo"),
                (qpi_poly.clone(), "qpi"),
            ]
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

        // let mut selector_oracles: Vec<_> = selector_commitments
        //     .iter()
        //     .map(|cmt| FixedVerifierOracle::<F, PC> {
        //         label: cmt.label().clone(),
        //         queried_rotations: BTreeSet::default(),
        //         evals_at_challenges: BTreeMap::default(),
        //         commitment: Some(cmt.commitment().clone()),
        //     })
        //     .collect();

        // let labeled_selectors: Vec<LabeledPolynomial<F, DensePolynomial<F>>> =
        //     [
        //         (qm_poly.clone(), "qm"),
        //         (ql_poly.clone(), "ql"),
        //         (qr_poly.clone(), "qr"),
        //         (qo_poly.clone(), "qo"),
        //         (qpi_poly.clone(), "qpi"),
        //     ]
        //     .iter()
        //     .map(|(poly, label)| {
        //         LabeledPolynomial::new(
        //             label.to_string(),
        //             poly.clone(),
        //             None,
        //             None,
        //         )
        //     })
        //     .collect();

        // let (selector_commitments, _) =
        //     PC::commit(&ck, labeled_selectors.iter(), None).unwrap();

        let mut selector_oracles: Vec<_> = selector_commitments
            .iter()
            .map(|cmt| FixedVerifierOracle::<F, PC> {
                label: cmt.label().clone(),
                queried_rotations: BTreeSet::default(),
                evals_at_challenges: BTreeMap::default(),
                commitment: Some(cmt.commitment().clone()),
            })
            .collect();

        let mut plonk_vo = GenericVO::<F, PC>::init(
            PrecompiledPlonkArith::get_expr_and_queries(),
        );

        plonk_vo.configure(
            &mut witness_ver_oracles,
            &mut instance_oracles,
            &mut selector_oracles,
        );

        let vos: Vec<&dyn VirtualOracle<F>> = vec![&plonk_vo];

        // Repeat but this time provide verifier witness oracles
        let mut vk = Indexer::index(
            &verifier_key,
            &vos,
            &witness_ver_oracles,
            &instance_oracles,
            &selector_oracles,
            domain,
            &domain.vanishing_polynomial().into(),
            None,
        )
        .unwrap();

        let verifier_pp = VerifierPreprocessedInput {
            fixed_oracles: selector_oracles.clone(),
            permutation_oracles: vec![],
            q_blind: None,
        };

        // We clone because fixed oracles must be mutable in order to add evals at challenge
        // Another option is to create reset method which will just reset challenge to eval mapping
        // This is anyway just mockup of frontend
        let mut pp_clone = verifier_pp.clone();

        let res = PilInstance::verify(
            &mut vk,
            &mut pp_clone,
            proof,
            &mut witness_ver_oracles,
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
