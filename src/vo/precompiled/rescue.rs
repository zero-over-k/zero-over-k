use super::PrecompiledVO;
use crate::{
    oracles::{query::OracleType, rotation::Rotation},
    vo::{query::VirtualQuery, virtual_expression::VirtualExpression},
};
use ark_ff::PrimeField;

/// Rescue VO implements a 4 element vector multiplication and a exponentiation:
/// (q1, q2, q3, q4) * (w1, w2, w3, w4)^5  = w5
/// Constraint :
/// q_1 * w_1^5 +
/// q_2 * w_2^5 +
/// q_3 * w_3^5 +
/// q_4 * w_4^5 -
/// w_5 = 0
pub struct PrecompiledRescue {}

impl<F> PrecompiledVO<F> for PrecompiledRescue
where
    F: PrimeField,
{
    fn get_expr_and_queries() -> (VirtualExpression<F>, Vec<VirtualQuery>) {
        let q = (0..=3).map(|index| {
            VirtualQuery::new(index, Rotation::curr(), OracleType::Fixed)
        });
        let w = (0..=4).map(|index| {
            VirtualQuery::new(index, Rotation::curr(), OracleType::Witness)
        });
        let oracles = q.clone().chain(w.clone()).collect();

        let rescue_expr = {
            let q_expr: Vec<VirtualExpression<F>> =
                q.map(|query| query.into()).collect();
            let w_expr: Vec<VirtualExpression<F>> =
                w.map(|query| query.into()).collect();
            let pow_5 = |e: &VirtualExpression<F>| {
                e.clone() * e.clone() * e.clone() * e.clone() * e.clone()
            };

            q_expr[0].clone() * pow_5(&w_expr[0])
                + q_expr[1].clone() * pow_5(&w_expr[1])
                + q_expr[2].clone() * pow_5(&w_expr[2])
                + q_expr[3].clone() * pow_5(&w_expr[3])
                - w_expr[4].clone()
        };

        (rescue_expr, oracles)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use std::collections::BTreeSet;

    use ark_bls12_381::{Bls12_381, Fr};
    use ark_ff::Zero;
    use ark_poly::Polynomial;
    use ark_poly::{
        univariate::DensePolynomial, EvaluationDomain, GeneralEvaluationDomain,
        UVPolynomial,
    };

    use ark_std::test_rng;
    use rand_chacha::ChaChaRng;

    use crate::oracles::fixed::FixedProverOracle;
    use crate::oracles::instance::InstanceProverOracle;

    use crate::oracles::traits::Instantiable;
    use crate::oracles::witness::WitnessProverOracle;
    use crate::rng::SimpleHashFiatShamirRng;
    use crate::vo::generic_vo::GenericVO;
    use crate::PIL;
    use blake2::Blake2s;

    use crate::commitment::KZG10;
    use crate::vo::VirtualOracle;

    use itertools::izip;

    type F = Fr;
    type FS = SimpleHashFiatShamirRng<Blake2s, ChaChaRng>;
    type PC = KZG10<Bls12_381>;

    type PilInstance = PIL<F, PC, FS>;

    // #[test]
    // fn test_rescue_gate() {
    //     let mut rescue_vo =
    //         GenericVO::<F, PC>::init(PrecompiledRescue::get_expr_and_queries());

    //     let mut witness_oracles: Vec<_> = ["a", "b", "c", "d", "e"]
    //         .into_iter()
    //         .map(|label| WitnessProverOracle::<F> {
    //             label: label.to_string(),
    //             poly: DensePolynomial::default(),
    //             evals_at_coset_of_extended_domain: None,
    //             queried_rotations: BTreeSet::new(),
    //             should_permute: false,
    //             evals: vec![F::zero(); 0],
    //         })
    //         .collect();

    //     let mut instance_oracles: Vec<InstanceProverOracle<F>> = vec![];

    //     let mut fixed_oracles: Vec<_> = ["q1", "q2", "q3", "q4"]
    //         .into_iter()
    //         .map(|label| FixedProverOracle::<F> {
    //             label: label.to_string(),
    //             poly: DensePolynomial::default(),
    //             evals_at_coset_of_extended_domain: None,
    //             evals: vec![F::zero(); 0],
    //             queried_rotations: BTreeSet::default(),
    //         })
    //         .collect();

    //     rescue_vo.configure(
    //         &mut witness_oracles,
    //         &mut instance_oracles,
    //         &mut fixed_oracles,
    //     );
    // }

    #[test]
    fn test_rescue_gate() {
        let max_degree = 15;
        let mut rng = test_rng();

        let srs = PilInstance::universal_setup(max_degree, &mut rng).unwrap();

        let (_ck, _verifier_key) = PilInstance::prepare_keys(&srs).unwrap();

        let domain_size = 16;
        let poly_degree = domain_size - 1;
        let domain = GeneralEvaluationDomain::<F>::new(domain_size).unwrap();

        let witness_polys: Vec<_> = (0..=4)
            .map(|_| DensePolynomial::<F>::rand(poly_degree, &mut rng))
            .collect();
        let witness_evals: Vec<Vec<F>> =
            witness_polys.iter().map(|poly| domain.fft(&poly)).collect();

        let selector_polys: Vec<_> = (0..=3)
            .map(|_| DensePolynomial::<F>::rand(poly_degree, &mut rng))
            .collect();
        let fixed_evals: Vec<Vec<F>> = selector_polys
            .iter()
            .map(|poly| domain.fft(&poly))
            .collect();

        let pow_5 = |v: &F| *v * v * v * v * v;
        let w5_evals: Vec<F> = izip!(
            &witness_evals[0],
            &witness_evals[1],
            &witness_evals[2],
            &witness_evals[3],
            &witness_evals[4],
            &fixed_evals[0],
            &fixed_evals[1],
            &fixed_evals[2],
            &fixed_evals[3],
        )
        .map(|(w1, w2, w3, w4, _w5, &q1, &q2, &q3, &q4)| {
            q1 * pow_5(w1) + q2 * pow_5(w2) + q3 * pow_5(w3) + q4 * pow_5(w4)
            // - pow_5(w5) //TODO: should this value be here
        })
        .collect();

        let w5_poly =
            DensePolynomial::from_coefficients_slice(&domain.ifft(&w5_evals));

        let mut rescue_vo =
            GenericVO::<F>::init(PrecompiledRescue::get_expr_and_queries());

        let mut witness_oracles: Vec<_> = [
            (witness_polys[0].clone(), witness_evals[0].clone(), "a"),
            (witness_polys[1].clone(), witness_evals[1].clone(), "b"),
            (witness_polys[2].clone(), witness_evals[2].clone(), "c"),
            (witness_polys[3].clone(), witness_evals[3].clone(), "d"),
            (w5_poly, w5_evals.clone(), "e"),
        ]
        .into_iter()
        .map(|(poly, evals, label)| WitnessProverOracle::<F> {
            label: label.to_string(),
            poly,
            evals_at_coset_of_extended_domain: None,
            queried_rotations: BTreeSet::new(),
            should_permute: false,
            evals,
        })
        .collect();

        let mut instance_oracles: Vec<InstanceProverOracle<F>> = vec![];

        let mut selector_oracles: Vec<_> = [
            (selector_polys[0].clone(), "q1"),
            (selector_polys[1].clone(), "q2"),
            (selector_polys[2].clone(), "q3"),
            (selector_polys[3].clone(), "q4"),
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

        rescue_vo.configure(
            &mut witness_oracles,
            &mut instance_oracles,
            &mut selector_oracles,
        );

        // q_expr[0].clone() * pow_5(&w_expr[0])
        // + q_expr[1].clone() * pow_5(&w_expr[1])
        // + q_expr[2].clone() * pow_5(&w_expr[2])
        // + q_expr[3].clone() * pow_5(&w_expr[3])
        // - w_expr[4].clone()
        for elem in domain.elements() {
            let q1 = selector_oracles[0].polynomial().evaluate(&elem);
            let q2 = selector_oracles[1].polynomial().evaluate(&elem);
            let q3 = selector_oracles[2].polynomial().evaluate(&elem);
            let q4 = selector_oracles[3].polynomial().evaluate(&elem);

            let w1 = witness_oracles[0].polynomial().evaluate(&elem);
            let w2 = witness_oracles[1].polynomial().evaluate(&elem);
            let w3 = witness_oracles[2].polynomial().evaluate(&elem);
            let w4 = witness_oracles[3].polynomial().evaluate(&elem);
            let wpow5 = witness_oracles[4].polynomial().evaluate(&elem);

            let rescue = q1 * pow_5(&w1)
                + q2 * pow_5(&w2)
                + q3 * pow_5(&w3)
                + q4 * pow_5(&w4)
                - wpow5;

            assert_eq!(rescue, F::zero())
        }

        let _vos: Vec<&dyn VirtualOracle<F>> = vec![&rescue_vo];

        // let vk = Indexer::index(
        //     &verifier_key,
        //     &vos,
        //     &witness_oracles,
        //     &instance_oracles,
        //     &selector_oracles,
        //     domain,
        //     &domain.vanishing_polynomial().into(),
        //     None,
        // )
        // .unwrap();

        // let pk = ProverKey::from_ck_and_vk(&ck, &vk);

        // let preprocessed = ProverPreprocessedInput::new(
        //     &selector_oracles,
        //     &vec![],
        //     None,
        //     &vk.index_info,
        // );

        // let proof = PilInstance::prove(
        //     &pk,
        //     &preprocessed,
        //     &mut witness_oracles,
        //     &mut instance_oracles,
        //     &vos,
        //     domain_size,
        //     &domain.vanishing_polynomial().into(),
        //     &mut rng,
        // )
        // .unwrap();

        // println!("{}", proof.info());
        // println!("{}", proof.cumulative_info());
        // println!("in bytes: {}", proof.serialized_size());

        // Verifier
        // Repeat everything to make sure that we are not implicitly using something from prover

        // let mut witness_ver_oracles: Vec<_> = ["a", "b", "c", "d", "e"]
        //     .into_iter()
        //     .map(|label| WitnessVerifierOracle::<F, PC> {
        //         label: label.to_string(),
        //         queried_rotations: BTreeSet::new(),
        //         should_permute: false,
        //         evals_at_challenges: BTreeMap::default(),
        //         commitment: None,
        //     })
        //     .collect();

        // let mut instance_oracles: [InstanceVerifierOracle<F>; 0] = [];

        // let labeled_selectors: Vec<LabeledPolynomial<F, DensePolynomial<F>>> =
        //     [
        //         (selector_polys[0].clone(), "q1"),
        //         (selector_polys[1].clone(), "q2"),
        //         (selector_polys[2].clone(), "q3"),
        //         (selector_polys[3].clone(), "q4"),
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

        // let mut selector_oracles: Vec<_> = selector_commitments
        //     .iter()
        //     .map(|cmt| FixedVerifierOracle::<F, PC> {
        //         label: cmt.label().clone(),
        //         queried_rotations: BTreeSet::default(),
        //         evals_at_challenges: BTreeMap::default(),
        //         commitment: Some(cmt.commitment().clone()),
        //     })
        //     .collect();

        // let mut rescue_vo =
        //     GenericVO::<F, PC>::init(PrecompiledRescue::get_expr_and_queries());

        // rescue_vo.configure(
        //     &mut witness_ver_oracles,
        //     &mut instance_oracles,
        //     &mut selector_oracles,
        // );

        // let vk = Indexer::index(
        //     &verifier_key,
        //     &vos,
        //     &witness_ver_oracles,
        //     &instance_oracles,
        //     &selector_oracles,
        //     domain,
        //     &domain.vanishing_polynomial().into(),
        //     None,
        // )
        // .unwrap();

        // let verifier_pp = VerifierPreprocessedInput {
        //     fixed_oracles: selector_oracles.clone(),
        //     permutation_oracles: vec![],
        //     q_blind: None,
        // };

        // We clone because fixed oracles must be mutable in order to add evals at challenge
        // Another option is to create reset method which will just reset challenge to eval mapping
        // This is anyway just mockup of frontend
        // let mut pp_clone = verifier_pp.clone();

        // let vos: Vec<&dyn VirtualOracle<F>> = vec![&rescue_vo];

        // let res = PilInstance::verify(
        //     &vk,
        //     &mut pp_clone,
        //     proof,
        //     &mut witness_ver_oracles,
        //     &mut [],
        //     &vos,
        //     domain_size,
        //     &domain.vanishing_polynomial().into(),
        //     &mut rng,
        // )
        // .unwrap();

        // assert_eq!(res, ());
    }
}
