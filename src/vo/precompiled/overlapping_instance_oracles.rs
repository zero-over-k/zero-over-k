/*
 * Two gates to create the following equation:
 * (a * b - p1) + (c * d - p1) = 0
 *
 * Gate 1: a * b - p1 = 0
 * Gate 2: c * d - p1 = 0
 *
 * Solution:
 * a = 5
 * b = 6
 * c = 3
 * d = 10
 * p1 = 30 (sicne 5*6 = 3*10)
 */

use ark_ff::PrimeField;
use crate::{vo::{virtual_expression::VirtualExpression, query::VirtualQuery}, oracles::{query::OracleType, rotation::Rotation}};


pub fn get_expr_and_queries<F: PrimeField>() -> (VirtualExpression<F>, Vec<VirtualQuery>) {
    let a = VirtualQuery::new(0, Rotation::curr(), OracleType::Witness);
    let b = VirtualQuery::new(1, Rotation::curr(), OracleType::Witness);

    let pi = VirtualQuery::new(0, Rotation::curr(), OracleType::Instance);


    let gate_expr = {
        let a: VirtualExpression<F> = a.clone().into();
        let b: VirtualExpression<F> = b.clone().into();
        let pi: VirtualExpression<F> = pi.clone().into();

        a * b - pi
    };

    (gate_expr, vec![a, b, pi])
}

#[cfg(test)]
mod tests {
    use std::vec;
    use super::get_expr_and_queries;

    use ark_bls12_381::{Bls12_381, Fr as F};
    use ark_ff::Zero;
    use ark_poly::{GeneralEvaluationDomain, EvaluationDomain, univariate::DensePolynomial, UVPolynomial, Polynomial};
    use ark_std::test_rng;
    use blake2::Blake2s;
    use rand_chacha::ChaChaRng;
    use crate::{rng::SimpleHashFiatShamirRng, commitment::{KZG10, HomomorphicCommitment}, PIL, oracles::{witness::{WitnessProverOracle, WitnessVerifierOracle}, fixed::{FixedProverOracle, FixedVerifierOracle}, instance::{InstanceProverOracle, InstanceVerifierOracle}}, vo::{generic_vo::GenericVO, VirtualOracle}, indexer::Indexer, data_structures::{PermutationInfo, ProverKey, ProverPreprocessedInput, VerifierPreprocessedInput}};

    type FS = SimpleHashFiatShamirRng<Blake2s, ChaChaRng>;
    type PC = KZG10<Bls12_381>;

    type PilInstance = PIL<F, PC, FS>;

    #[test]
    fn test_overlapping_instance_oracles() {
        let mut rng = test_rng();

        let domain_size = 16;
        let domain = GeneralEvaluationDomain::<F>::new(domain_size).unwrap();
        let poly_degree = domain_size - 1;
        let max_degree = poly_degree;

        let srs = PilInstance::universal_setup(max_degree, &mut rng).unwrap();
        let (ck, verifier_key) = PilInstance::prepare_keys(&srs).unwrap();

        let a_evals = vec![F::from(5u64); domain_size];
        let a_poly = DensePolynomial::from_coefficients_slice(&domain.ifft(&a_evals));

        let b_evals = vec![F::from(6u64); domain_size];
        let b_poly = DensePolynomial::from_coefficients_slice(&domain.ifft(&b_evals));

        let c_evals = vec![F::from(3u64); domain_size];
        let c_poly = DensePolynomial::from_coefficients_slice(&domain.ifft(&c_evals));

        let d_evals = vec![F::from(10u64); domain_size];
        let d_poly = DensePolynomial::from_coefficients_slice(&domain.ifft(&d_evals));

        let pi_evals = vec![F::from(30u64); domain_size];
        let pi_poly = DensePolynomial::from_coefficients_slice(&domain.ifft(&pi_evals));

        for elem in domain.elements() {
            assert_eq!(
                a_poly.evaluate(&elem) *
                b_poly.evaluate(&elem)
                    - pi_poly.evaluate(&elem),
                F::zero()
            );
            assert_eq!(
                c_poly.evaluate(&elem) *
                d_poly.evaluate(&elem)
                    - pi_poly.evaluate(&elem),
                F::zero()
            );
        }

        // (a * b - pi) + (c * a - pi) = 0

        let mut a = WitnessProverOracle::new("a", a_poly, &a_evals, false);
        let mut b = WitnessProverOracle::new("b", b_poly, &b_evals, false);
        let mut c = WitnessProverOracle::new("c", c_poly, &c_evals, false);
        let mut d = WitnessProverOracle::new("d", d_poly, &d_evals, false);

        let mut pi = InstanceProverOracle::new("pi", pi_poly.clone(), &pi_evals);

        let mut gate_1_vo = GenericVO::<F>::init(get_expr_and_queries());
        let mut gate_2_vo = GenericVO::<F>::init(get_expr_and_queries());

        // Note that vo.configure MUTATES each witness oracle
        let mut gate_1_witness_oracles: &mut [&mut WitnessProverOracle<F>] = &mut [&mut a, &mut b];
        let mut gate_1_instance_oracles: &mut [&mut InstanceProverOracle<F>] = &mut [&mut pi];
        let mut gate_1_fixed_oracles = &mut [] as &mut [&mut FixedProverOracle<F>];

        gate_1_vo.configure(
            &mut gate_1_witness_oracles,
            &mut gate_1_instance_oracles,
            &mut gate_1_fixed_oracles,
        );

        let mut gate_2_witness_oracles: &mut [&mut WitnessProverOracle<F>] = &mut [&mut c, &mut d];
        let mut gate_2_instance_oracles: &mut [&mut InstanceProverOracle<F>] = &mut [&mut pi];
        let mut gate_2_fixed_oracles = &mut [] as &mut [&mut FixedProverOracle<F>];

        gate_2_vo.configure(
            &mut gate_2_witness_oracles,
            &mut gate_2_instance_oracles,
            &mut gate_2_fixed_oracles,
        );

        // witness_oracles should contain the CONFIGURED witness oracles.
        // Can't be [&mut a, &mut b, &mut c, &mut a] because Rust won't allow &mut a twice
        let mut witness_oracles: &mut [&mut WitnessProverOracle<F>] = &mut [&mut a, &mut b, &mut c, &mut d];

        let prover_fixed_oracles = &mut [] as &mut [&mut FixedProverOracle<F>];
        let mut verifier_fixed_oracles = &mut [] as &mut [&mut FixedVerifierOracle<F, PC>];

        let mut instance_oracles: &mut [&mut InstanceProverOracle<F>] = &mut [&mut pi];

        let vos: Vec<&dyn VirtualOracle<F>> = vec![&gate_1_vo, &gate_2_vo];

        let vk = Indexer::index(
            &verifier_key,
            &vos,
            vec![],
            &witness_oracles,
            &instance_oracles,
            &verifier_fixed_oracles,
            domain,
            &domain.vanishing_polynomial().into(),
            PermutationInfo::dummy(),
            0,
        )
        .unwrap();

        let pk = ProverKey::from_ck_and_vk(&ck, &vk);

        let q_blind = FixedProverOracle::new("q_blind", DensePolynomial::zero(), &vec![]);

        let mut preprocessed = ProverPreprocessedInput::new(
            prover_fixed_oracles,
            &vec![],
            &vec![],
            &q_blind,
            &vk.index_info,
        );

        let proof = PilInstance::prove(
            &pk,
            &mut preprocessed,
            &mut witness_oracles,
            &mut instance_oracles,
            &vos,
            domain_size,
            &domain.vanishing_polynomial().into(),
            &mut rng,
        )
        .unwrap();

        // Proof verification
        let mut w1 = WitnessVerifierOracle::new("a", false);
        let mut w2 = WitnessVerifierOracle::new("b", false);
        let mut w3 = WitnessVerifierOracle::new("c", false);
        let mut w4 = WitnessVerifierOracle::new("d", false);

        let mut pi = InstanceVerifierOracle::new("pi1", pi_poly.clone(), &pi_evals);

        //let mut fixed_oracles = &mut [] as &mut &[&mut FixedVerifierOracle<F, PC>];

        let mut gate_1_witness_oracles: &mut [&mut WitnessVerifierOracle<F, PC>] = &mut [&mut w1, &mut w2];
        let mut gate_1_instance_oracles: &mut [&mut InstanceVerifierOracle<F>] = &mut [&mut pi];

        let mut gate_1_vo = GenericVO::<F>::init(get_expr_and_queries());
        let mut gate_2_vo = GenericVO::<F>::init(get_expr_and_queries());

        gate_1_vo.configure(
            &mut gate_1_witness_oracles,
            &mut gate_1_instance_oracles,
            &mut verifier_fixed_oracles,
        );

        let mut gate_2_witness_oracles: &mut [&mut WitnessVerifierOracle<F, PC>] = &mut [&mut w3, &mut w4];
        let mut gate_2_instance_oracles: &mut [&mut InstanceVerifierOracle<F>] = &mut [&mut pi];

        gate_2_vo.configure(
            &mut gate_2_witness_oracles,
            &mut gate_2_instance_oracles,
            &mut verifier_fixed_oracles,
        );

        let mut witness_oracles: &mut [&mut WitnessVerifierOracle<F, PC>] = &mut [&mut w1, &mut w2, &mut w3, &mut w4];

        let mut instance_oracles: &mut [&mut InstanceVerifierOracle<F>] = &mut [&mut pi];

        let vos: Vec<&dyn VirtualOracle<F>> = vec![&gate_1_vo, &gate_2_vo];

        // Repeat but this time provide verifier witness oracles
        let mut vk = Indexer::index(
            &verifier_key,
            &vos,
            vec![],
            &mut witness_oracles,
            &instance_oracles,
            &mut verifier_fixed_oracles,
            domain,
            &domain.vanishing_polynomial().into(),
            PermutationInfo::dummy(),
            0,
        )
        .unwrap();

        let q_blind = FixedVerifierOracle::new("q_blind".to_string(), Some(PC::zero_comm()));

        let mut preprocessed = VerifierPreprocessedInput {
            fixed_oracles: verifier_fixed_oracles,
            table_oracles: vec![],
            permutation_oracles: vec![],
            q_blind,
        };

        let res = PilInstance::verify(
            &mut vk,
            &mut preprocessed,
            proof,
            &mut witness_oracles,
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
