/*
 * Two gates to create the following equation:
 * (a * b - p1) + (c * a - p2) = 0
 *
 * Gate 1: a * b - p1 = 0
 * Gate 2: c * a - p2 = 0
 *
 * Solution:
 * a = 1
 * b = p1 = any value
 * c = p2 = any value
 *
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
    use ark_ff::{Zero, One};
    use ark_poly::{GeneralEvaluationDomain, EvaluationDomain, univariate::DensePolynomial, UVPolynomial, Polynomial};
    use ark_std::test_rng;
    use blake2::Blake2s;
    use rand_chacha::ChaChaRng;
    use crate::{rng::SimpleHashFiatShamirRng, commitment::{KZG10, HomomorphicCommitment}, PIL, oracles::{witness::{WitnessProverOracle, WitnessVerifierOracle}, fixed::{FixedProverOracle, FixedVerifierOracle}, instance::{InstanceProverOracle, InstanceVerifierOracle}}, vo::{generic_vo::GenericVO, VirtualOracle}, indexer::Indexer, data_structures::{PermutationInfo, ProverKey, ProverPreprocessedInput, VerifierPreprocessedInput}};

    type FS = SimpleHashFiatShamirRng<Blake2s, ChaChaRng>;
    type PC = KZG10<Bls12_381>;

    type PilInstance = PIL<F, PC, FS>;

    #[test]
    fn test_overlapping_witness_oracles() {
        let mut rng = test_rng();

        let domain_size = 16;
        let domain = GeneralEvaluationDomain::<F>::new(domain_size).unwrap();
        let poly_degree = domain_size - 1;
        let max_degree = poly_degree;

        let srs = PilInstance::universal_setup(max_degree, &mut rng).unwrap();
        let (ck, verifier_key) = PilInstance::prepare_keys(&srs).unwrap();

         // a = 1
         // b = p1 = any value
         // c = p2 = any value
        let a_evals = vec![F::one(); domain_size];
        let a_poly = DensePolynomial::from_coefficients_slice(&domain.ifft(&a_evals));

        let b_poly = DensePolynomial::<F>::rand(poly_degree, &mut rng);
        let b_evals = domain.fft(&b_poly);
        let c_poly = DensePolynomial::<F>::rand(poly_degree, &mut rng);
        let c_evals = domain.fft(&c_poly);

        let pi1_evals = b_evals.clone();
        let pi1_poly = DensePolynomial::from_coefficients_slice(&domain.ifft(&pi1_evals));

        let pi2_evals = c_evals.clone();
        let pi2_poly = DensePolynomial::from_coefficients_slice(&domain.ifft(&pi2_evals));

        for elem in domain.elements() {
            assert_eq!(
                a_poly.evaluate(&elem) *
                b_poly.evaluate(&elem)
                    - pi1_poly.evaluate(&elem),
                F::zero()
            );
            assert_eq!(
                c_poly.evaluate(&elem) *
                a_poly.evaluate(&elem)
                    - pi2_poly.evaluate(&elem),
                F::zero()
            );
        }

        // (a * b - pi1) + (c * a - pi2) = 0

        let mut a = WitnessProverOracle::new("a", a_poly, &a_evals, false);
        let mut b = WitnessProverOracle::new("b", b_poly, &b_evals, false);
        let mut c = WitnessProverOracle::new("c", c_poly, &c_evals, false);

        let pi1 = InstanceProverOracle::new("pi1", pi1_poly.clone(), &pi1_evals);
        let pi2 = InstanceProverOracle::new("pi2", pi2_poly.clone(), &pi2_evals);

        let mut gate_1_vo = GenericVO::<F>::init(get_expr_and_queries());
        let mut gate_2_vo = GenericVO::<F>::init(get_expr_and_queries());

        let fixed_oracles: Vec<FixedProverOracle<F>> = vec![];

        // Note that vo.configure MUTATES each witness oracle
        let mut gate_1_witness_oracles: &mut [&mut WitnessProverOracle<F>] = &mut [&mut a, &mut b];
        let mut gate_1_instance_oracles = vec![pi1.clone()];
        let mut gate_1_fixed_oracles: Vec<FixedVerifierOracle<F, PC>> = vec![];

        gate_1_vo.configure(
            &mut gate_1_witness_oracles,
            &mut gate_1_instance_oracles,
            &mut gate_1_fixed_oracles,
        );

        let mut gate_2_witness_oracles: &mut [&mut WitnessProverOracle<F>] = &mut [&mut c, &mut a];
        let mut gate_2_instance_oracles = vec![pi2.clone()];
        let mut gate_2_fixed_oracles: Vec<FixedVerifierOracle<F, PC>> = vec![];
        gate_2_vo.configure(
            &mut gate_2_witness_oracles,
            &mut gate_2_instance_oracles,
            &mut gate_2_fixed_oracles,
        );

        // witness_oracles should contain the CONFIGURED witness oracles.
        // Can't be [&mut a, &mut b, &mut c, &mut a] because Rust won't allow &mut a twice
        let mut witness_oracles: &mut [&mut WitnessProverOracle<F>] = &mut [&mut a, &mut b, &mut c];

        let mut instance_oracles = vec![];
        instance_oracles.extend(gate_1_instance_oracles.clone());
        instance_oracles.extend(gate_2_instance_oracles.clone());

        let vos: Vec<&dyn VirtualOracle<F>> = vec![&gate_1_vo, &gate_2_vo];

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

        let q_blind = FixedProverOracle::new("q_blind", DensePolynomial::zero(), &vec![]);

        let preprocessed = ProverPreprocessedInput::new(
            &fixed_oracles,
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

        // Proof verification
        let mut w1 = WitnessVerifierOracle::new("a", false);
        let mut w2 = WitnessVerifierOracle::new("b", false);
        let mut w3 = WitnessVerifierOracle::new("c", false);

        let pi1 = InstanceVerifierOracle::new("pi1", pi1_poly.clone(), &pi1_evals);
        let pi2 = InstanceVerifierOracle::new("pi2", pi2_poly.clone(), &pi2_evals);

        let fixed_oracles: Vec<FixedVerifierOracle<F, PC>> = vec![];

        let mut gate_1_witness_oracles: &mut [&mut WitnessVerifierOracle<F, PC>] = &mut [&mut w1, &mut w2];
        let mut gate_1_instance_oracles = vec![pi1];
        let mut gate_1_fixed_oracles: Vec<FixedVerifierOracle<F, PC>> = vec![];

        let mut gate_1_vo = GenericVO::<F>::init(get_expr_and_queries());
        let mut gate_2_vo = GenericVO::<F>::init(get_expr_and_queries());

        gate_1_vo.configure(
            &mut gate_1_witness_oracles,
            &mut gate_1_instance_oracles,
            &mut gate_1_fixed_oracles,
        );

        let mut gate_2_witness_oracles: &mut [&mut WitnessVerifierOracle<F, PC>] = &mut [&mut w3, &mut w1];
        let mut gate_2_instance_oracles = vec![pi2];
        let mut gate_2_fixed_oracles: Vec<FixedVerifierOracle<F, PC>> = vec![];

        gate_2_vo.configure(
            &mut gate_2_witness_oracles,
            &mut gate_2_instance_oracles,
            &mut gate_2_fixed_oracles,
        );

        let mut witness_oracles: &mut [&mut WitnessVerifierOracle<F, PC>] = &mut [&mut w1, &mut w2, &mut w3];

        let mut instance_oracles = vec![];
        instance_oracles.extend(gate_1_instance_oracles);
        instance_oracles.extend(gate_2_instance_oracles);

        let vos: Vec<&dyn VirtualOracle<F>> = vec![&gate_1_vo, &gate_2_vo];

        // Repeat but this time provide verifier witness oracles
        let mut vk = Indexer::index(
            &verifier_key,
            &vos,
            vec![],
            &mut witness_oracles,
            &instance_oracles,
            &fixed_oracles,
            domain,
            &domain.vanishing_polynomial().into(),
            PermutationInfo::dummy(),
            0,
        )
        .unwrap();

        let q_blind = FixedVerifierOracle::new("q_blind".to_string(), Some(PC::zero_comm()));

        let preprocessed = VerifierPreprocessedInput {
            fixed_oracles: fixed_oracles,
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
