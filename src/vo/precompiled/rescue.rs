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

    use ark_bls12_381::Fr;
    use ark_ff::UniformRand;
    use ark_poly::EvaluationDomain;

    use crate::vo::generic_vo::GenericVO;
    use crate::vo::precompiled::tests::{run_prover, run_verifier, test_init};

    use itertools::izip;

    type F = Fr;

    #[test]
    fn test_rescue_gate() {
        // Initialize context
        let (domain, cs_keys, mut rng) = test_init(4usize);

        // Generate circuit evals
        let domain_size = domain.size();
        let mut rand_evals =
            |num| (0..num).map(|_| F::rand(&mut rng)).collect();

        // let witness_polys: Vec<_> = (0..=4)
        //     .map(|_| DensePolynomial::<F>::rand(poly_degree, &mut rng))
        //     .collect();
        let witness_evals: Vec<Vec<F>> =
            (0..=4).map(|_| rand_evals(domain_size)).collect();
        let mut witness_labels = vec!["w_1", "w_2", "w_3", "w_4"]; //w_5 added later
        let mut witness: Vec<(_, &[F])> = witness_evals
            .iter()
            .zip(witness_labels.clone().into_iter())
            .map(|(evals, label)| (label, evals.as_slice()))
            .collect();

        let fixed_evals: Vec<Vec<F>> =
            (0..=3).map(|_| rand_evals(domain_size)).collect();
        let fixed_labels = vec!["q1", "q2", "q3", "q4"];
        let fixed: Vec<(_, &[F])> = fixed_evals
            .iter()
            .zip(fixed_labels.into_iter())
            .map(|(evals, label)| (label, evals.as_slice()))
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
        })
        .collect();
        witness_labels.append(&mut vec!["w_5"]);
        witness.append(&mut vec![("w_5", w5_evals.as_slice())]);

        let instance: Vec<(&str, &[F])> = vec![];
        // Run prover
        let rescue_vo =
            GenericVO::<F>::init(PrecompiledRescue::get_expr_and_queries());
        let proof = run_prover(
            domain,
            cs_keys.0.clone(),
            cs_keys.1.clone(),
            witness.clone(),
            fixed.clone(),
            instance.clone(),
            rescue_vo.clone(),
            &mut rng,
        );

        // Run verifier
        let res = run_verifier(
            domain,
            cs_keys.0,
            cs_keys.1,
            witness_labels,
            fixed,
            instance,
            rescue_vo,
            proof,
        );

        assert!(res.is_ok());
    }
}
