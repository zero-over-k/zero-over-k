use std::{collections::BTreeSet, marker::PhantomData};

use ark_ff::PrimeField;
use ark_poly::{
    univariate::DensePolynomial, EvaluationDomain, GeneralEvaluationDomain,
    UVPolynomial,
};
use ark_std::rand::RngCore;

use crate::{
    commitment::HomomorphicCommitment,
    oracles::{
        fixed::FixedOracle,
        instance::InstanceOracle,
        query::{OracleQuery, OracleType, QueryContext},
        rotation::Rotation,
        traits::{ConcreteOracle, Instantiable, WitnessOracle},
        witness::WitnessProverOracle,
    },
};

/// This module constructs one zero knowledge adjusted permutation check
/// (1 - (q_blind + q_last)) * (z(wX) * product_0,m-1 (vi(X) + beta*sigma_i(X) + gamma) - z(X) * product_0,m-1 (vi(X) + beta*sigma^i*X + gamma))
/// It isn't aware of outer context where splitting, copying across aggregation polynomials, beginning and ending checks are happening
pub struct GrandProductArgument<F: PrimeField, PC: HomomorphicCommitment<F>> {
    _field: PhantomData<F>,
    _pc: PhantomData<PC>,
}

impl<F: PrimeField, PC: HomomorphicCommitment<F>> GrandProductArgument<F, PC> {
    /// Given oracles constructs Z(X) polynomial that prover commits to
    pub fn construct_agg_poly<R: RngCore>(
        chunk_index: usize,
        permutation_oracles: &[FixedOracle<F, PC>],
        witness_oracles: &[WitnessProverOracle<F>],
        deltas: &[F],
        beta: F,
        gamma: F,
        u: usize, // allowed rows
        domain: &GeneralEvaluationDomain<F>,
        extended_coset_domain: &GeneralEvaluationDomain<F>,
        zk_rng: &mut R,
    ) -> WitnessProverOracle<F> {
        //TODO: store this evals in Oracles and enable some function from_evals
        let wi_evals: Vec<Vec<F>> = witness_oracles
            .iter()
            .map(|w| domain.fft(w.polynomial()))
            .collect();
        let sigma_evals: Vec<Vec<F>> = permutation_oracles
            .iter()
            .map(|sigma| domain.fft(sigma.polynomial()))
            .collect();

        let mut z_evals = Vec::<F>::with_capacity(domain.size());
        let mut z_prev = F::one();
        z_evals.push(z_prev);

        for i in 0..u {
            let mut nom = F::one();
            let mut denom = F::one();
            for ((w_i, sigma_i), &delta_i) in
                wi_evals.iter().zip(sigma_evals.iter()).zip(deltas.iter())
            {
                nom *= w_i[i] + beta * delta_i * domain.element(i) + gamma;
                denom *= w_i[i] + beta * sigma_i[i] + gamma;
            }

            z_prev *= nom * denom.inverse().unwrap();
            z_evals.push(z_prev);
        }

        // sanity
        assert_eq!(F::one(), z_evals[u]);

        // allowed rows is: u = domain_size - t - 1
        // t = domain_size - 1 - u
        // so blind with t evals
        let t = domain.size() - 1 - u;
        for _ in 0..t {
            z_evals.push(F::rand(zk_rng));
        }

        let z_poly =
            DensePolynomial::from_coefficients_slice(&domain.ifft(&z_evals));
        let evals_at_coset_of_extended_domain =
            Some(extended_coset_domain.coset_fft(&z_poly));

        WitnessProverOracle {
            label: format!("agg_permutation_{}", chunk_index).to_string(),
            poly: z_poly,
            evals_at_coset_of_extended_domain,
            queried_rotations: BTreeSet::from([
                Rotation::curr(),
                Rotation::next(),
            ]),
            should_mask: false,
        }
    }

    pub fn instantiate_argument(
        q_last: &FixedOracle<F, PC>,
        q_blind: &FixedOracle<F, PC>,
        z: &impl WitnessOracle<F>,
        permutation_oracles: &[FixedOracle<F, PC>],
        witness_oracles: &[impl WitnessOracle<F>],
        deltas: &[F],
        beta: F,
        gamma: F,
        domain: &GeneralEvaluationDomain<F>,
        extended_coset_domain: &GeneralEvaluationDomain<F>,
    ) -> Vec<F> {
        let mut grand_product_evals =
            Vec::with_capacity(extended_coset_domain.size());
        let domain_size = domain.size();
        for i in 0..extended_coset_domain.size() {
            let zk_ctx = QueryContext::<F>::ExtendedCoset(
                domain_size,
                Rotation::curr(),
                i,
            );
            let zk_part =
                F::one() - (q_last.query(&zk_ctx) + q_blind.query(&zk_ctx));

            let z_wx_ctx = QueryContext::<F>::ExtendedCoset(
                domain_size,
                Rotation::next(),
                i,
            );

            let mut lhs = z.query(&z_wx_ctx);

            let z_x_ctx = QueryContext::<F>::ExtendedCoset(
                domain_size,
                Rotation::curr(),
                i,
            );
            let mut rhs = z.query(&z_x_ctx);

            let oracle_ctx = QueryContext::<F>::ExtendedCoset(
                domain_size,
                Rotation::curr(),
                i,
            );
            for ((w_i, sigma_i), &delta_i) in witness_oracles
                .iter()
                .zip(permutation_oracles.iter())
                .zip(deltas.iter())
            {
                let w_res = w_i.query(&oracle_ctx);
                lhs *= w_res + beta * sigma_i.query(&oracle_ctx) + gamma;
                rhs *= w_res
                    + beta
                        * delta_i
                        * F::multiplicative_generator()
                        * extended_coset_domain.element(i)
                    + gamma;
            }

            grand_product_evals.push(zk_part * (lhs - rhs));
        }

        grand_product_evals
    }

    pub fn open_argument(
        q_last: &FixedOracle<F, PC>,
        q_blind: &FixedOracle<F, PC>,
        z: &impl WitnessOracle<F>,
        permutation_oracles: &[FixedOracle<F, PC>],
        witness_oracles: &[impl WitnessOracle<F>],
        deltas: &[F],
        beta: F,
        gamma: F,
        domain: &GeneralEvaluationDomain<F>,
        evaluation_challenge: F,
    ) -> F {
        let opening_ctx = QueryContext::Challenge(evaluation_challenge);
        let shifted_evaluation_challenge =
            domain.element(1) * evaluation_challenge;
        let shifted_opening_ctx =
            QueryContext::Challenge(shifted_evaluation_challenge);
        let zk_part = F::one()
            - (q_last.query(&opening_ctx) + q_blind.query(&opening_ctx));

        let mut lhs = z.query(&shifted_opening_ctx);
        let mut rhs = z.query(&opening_ctx);

        for ((w_i, sigma_i), &delta_i) in witness_oracles
            .iter()
            .zip(permutation_oracles.iter())
            .zip(deltas.iter())
        {
            let w_res = w_i.query(&opening_ctx);
            lhs *= w_res + beta * sigma_i.query(&opening_ctx) + gamma;
            rhs *= w_res + beta * delta_i * evaluation_challenge + gamma;
        }

        zk_part * (lhs - rhs)
    }
}

#[cfg(test)]
mod test {
    use std::collections::{BTreeMap, BTreeSet};

    use ark_ff::{FftField, Field, One, UniformRand, Zero};
    use ark_poly::{
        univariate::DensePolynomial, EvaluationDomain, GeneralEvaluationDomain,
        Polynomial, UVPolynomial,
    };

    use super::GrandProductArgument;
    use crate::{
        commitment::KZG10,
        oracles::{
            fixed::FixedOracle, rotation::Rotation,
            witness::WitnessProverOracle,
        },
        permutation,
    };

    use ark_bls12_381::{Bls12_381, Fr as F};
    use ark_std::test_rng;

    type PC = KZG10<Bls12_381>;

    #[test]
    fn x_in_coset() {
        let domain = GeneralEvaluationDomain::<F>::new(4).unwrap();
        let x =
            DensePolynomial::from_coefficients_slice(&[F::zero(), F::one()]);

        for elem in domain.elements() {
            println!("x: {}", x.evaluate(&elem));
        }

        let a = F::multiplicative_generator();
        println!("==========");

        let coset_evals = domain.coset_fft(&x);
        for eval in &coset_evals {
            println!("x coset: {}", eval);
        }

        println!("==========");

        for i in 0..4 {
            println!("{}", a * domain.element(i));
        }
    }

    #[test]
    fn test_product_argument() {
        /*
            k = 4
            domain_size = 2^k = 8
            t = 2
            usable = domain_size - t - 1 = 8 - 3 = 5
            q_blind = [0, 0, 0, 0, 0, 0, 1, 1]
            q_last =  [0, 0, 0, 0, 0, 1, 0, 0]

            a = [a0, a1, a2, a3, a4, blind, blind, blind]
            b = [b0, b1, b2, b3, b4, blind, blind, blind]

            z = [1, a0/b0, z1 * a1/b1, z2 * a2/b2, z3 * a3/b3, z4 * a4/b4, blind, blind]

            cycles = (a0, b1, b2, a4) (a2) (b0) (a1, b3, a3, b4)

            delta_0 = 1
            delta_1 = d

            sigma_1:   a0->b1, a1->b3, a2->a2, a3->b4, a4->a0, dummy, dummy, dummy
            sigma_1 =   dw      dw^3     w^2     dw^4    1     dummy  dummy  dummy

            sigma_2:  b0->b0, b1->b2, b2->a4, b3->a3, b4->a1, dummy, dummy, dummy
            sigma_2 =   d       dw^2    w^4     w^3     w     dummy  dummy  dummy
        */

        let mut rng = test_rng();

        let domain_size = 8;
        let domain = GeneralEvaluationDomain::<F>::new(domain_size).unwrap();

        let t = 2;
        let u = domain_size - t - 1;

        let q_blind_evals = [
            F::zero(),
            F::zero(),
            F::zero(),
            F::zero(),
            F::zero(),
            F::zero(),
            F::one(),
            F::one(),
        ];
        let q_last_evals = [
            F::zero(),
            F::zero(),
            F::zero(),
            F::zero(),
            F::zero(),
            F::one(),
            F::zero(),
            F::zero(),
        ];

        // cycle 1: (a0, b1, b2, a4)
        let a0 = F::rand(&mut rng);
        let b1 = a0;
        let b2 = a0;
        let a4 = a0;

        // cycle 2: (a2)
        let a2 = F::rand(&mut rng);

        // cycle 3: (b0)
        let b0 = F::rand(&mut rng);

        // cycle 4: (a1, b3, a3, b4)
        let a1 = F::rand(&mut rng);
        let b3 = a1;
        let a3 = a1;
        let b4 = a1;

        // blinds
        let a5 = F::rand(&mut rng);
        let a6 = F::rand(&mut rng);
        let a7 = F::rand(&mut rng);
        let b5 = F::rand(&mut rng);
        let b6 = F::rand(&mut rng);
        let b7 = F::rand(&mut rng);

        let a_evals = vec![a0, a1, a2, a3, a4, a5, a6, a7];
        let b_evals = vec![b0, b1, b2, b3, b4, b5, b6, b7];

        let dummy = F::rand(&mut rng);
        let d = F::from(13u64);
        let omegas: Vec<F> = domain.elements().collect();

        // sigma_1 =   dw      dw^3     w^2     dw^4    1     dummy  dummy  dummy
        let sigma_1_evals = vec![
            d * omegas[1],
            d * omegas[3],
            omegas[2],
            d * omegas[4],
            omegas[0],
            dummy,
            dummy,
            dummy,
        ];

        // sigma_2 =   d    dw^2   w^4     w^3     w     dummy  dummy  dummy
        let sigma_2_evals = vec![
            d,
            d * omegas[2],
            omegas[4],
            omegas[3],
            omegas[1],
            dummy,
            dummy,
            dummy,
        ];

        let beta = F::rand(&mut rng);
        let gamma = F::rand(&mut rng);

        let mut z_evals = vec![];
        let mut z_prev = F::one();
        z_evals.push(z_prev);

        for i in 0..u {
            let nom_a = a_evals[i] + beta * omegas[i] + gamma;
            let nom_b = b_evals[i] + beta * d * omegas[i] + gamma;

            let denom_a = a_evals[i] + beta * sigma_1_evals[i] + gamma;
            let denom_b = b_evals[i] + beta * sigma_2_evals[i] + gamma;

            let nom = nom_a * nom_b;
            let denom = denom_a * denom_b;

            z_prev *= nom * denom.inverse().unwrap();
            z_evals.push(z_prev);
        }

        assert_eq!(z_evals[u], F::one());
        // push 2 blinds
        z_evals.push(F::rand(&mut rng));
        z_evals.push(F::rand(&mut rng));

        // tmp just push first z_eval for easier querying z[wX] in last w
        z_evals.push(F::one());

        // Sanity check
        for (i, element) in domain.elements().enumerate() {
            let zk_part = F::one() - (q_blind_evals[i] + q_last_evals[i]);

            let lhs = {
                let z_wx = z_evals[i + 1];
                let a_part = a_evals[i] + beta * sigma_1_evals[i] + gamma;
                let b_part = b_evals[i] + beta * sigma_2_evals[i] + gamma;

                z_wx * a_part * b_part
            };

            let rhs = {
                let zw = z_evals[i];
                let a_part = a_evals[i] + beta * element + gamma;
                let b_part = b_evals[i] + beta * d * element + gamma;

                zw * a_part * b_part
            };

            assert_eq!(zk_part * (lhs - rhs), F::zero());
        }

        let a = DensePolynomial::<F>::from_coefficients_slice(
            &domain.ifft(&a_evals),
        );

        let b = DensePolynomial::<F>::from_coefficients_slice(
            &domain.ifft(&b_evals),
        );

        let q_last = DensePolynomial::<F>::from_coefficients_slice(
            &domain.ifft(&q_last_evals),
        );
        let q_blind = DensePolynomial::<F>::from_coefficients_slice(
            &domain.ifft(&q_blind_evals),
        );

        let sigma_1 = DensePolynomial::<F>::from_coefficients_slice(
            &domain.ifft(&sigma_1_evals),
        );

        let sigma_2 = DensePolynomial::<F>::from_coefficients_slice(
            &domain.ifft(&sigma_2_evals),
        );

        let z_poly = DensePolynomial::<F>::from_coefficients_slice(
            &domain.ifft(&z_evals),
        );

        // (q_last * a * b * z) / zh = 4n - 4 - n = 3n - 4 so we can work in 4n domain
        let extended_coset_domain =
            GeneralEvaluationDomain::<F>::new(4 * domain_size).unwrap();

        let a = WitnessProverOracle {
            label: "a".to_string(),
            poly: a.clone(),
            evals_at_coset_of_extended_domain: Some(
                extended_coset_domain.coset_fft(&a),
            ),
            queried_rotations: BTreeSet::from([Rotation::curr()]),
            should_mask: false,
        };

        let b = WitnessProverOracle {
            label: "b".to_string(),
            poly: b.clone(),
            evals_at_coset_of_extended_domain: Some(
                extended_coset_domain.coset_fft(&b),
            ),
            queried_rotations: BTreeSet::from([Rotation::curr()]),
            should_mask: false,
        };

        let sigma_1 = FixedOracle::<F, PC> {
            label: "sigma_1".to_string(),
            poly: sigma_1.clone(),
            evals_at_coset_of_extended_domain: Some(
                extended_coset_domain.coset_fft(&sigma_1),
            ),
            queried_rotations: BTreeSet::from([Rotation::curr()]),
            evals_at_challenges: BTreeMap::default(),
            commitment: None,
        };

        let sigma_2 = FixedOracle::<F, PC> {
            label: "sigma_2".to_string(),
            poly: sigma_2.clone(),
            evals_at_coset_of_extended_domain: Some(
                extended_coset_domain.coset_fft(&sigma_2),
            ),
            queried_rotations: BTreeSet::from([Rotation::curr()]),
            evals_at_challenges: BTreeMap::default(),
            commitment: None,
        };

        let q_blind = FixedOracle::<F, PC> {
            label: "q_blind".to_string(),
            poly: q_blind.clone(),
            evals_at_coset_of_extended_domain: Some(
                extended_coset_domain.coset_fft(&q_blind),
            ),
            queried_rotations: BTreeSet::from([Rotation::curr()]),
            evals_at_challenges: BTreeMap::default(),
            commitment: None,
        };

        let q_last = FixedOracle::<F, PC> {
            label: "q_last".to_string(),
            poly: q_last.clone(),
            evals_at_coset_of_extended_domain: Some(
                extended_coset_domain.coset_fft(&q_last),
            ),
            queried_rotations: BTreeSet::from([Rotation::curr()]),
            evals_at_challenges: BTreeMap::default(),
            commitment: None,
        };

        let witness_oracles = [a, b];
        let permutation_oracles = [sigma_1, sigma_2];

        let deltas = [F::one(), F::from(13u64)];

        let agg_poly = GrandProductArgument::<F, PC>::construct_agg_poly(
            0,
            &permutation_oracles,
            &witness_oracles,
            &deltas,
            beta,
            gamma,
            u,
            &domain,
            &extended_coset_domain,
            &mut rng,
        );

        // they differ in blinding
        for i in 0..=u {
            assert_eq!(
                agg_poly.poly.evaluate(&domain.element(i)),
                z_poly.evaluate(&domain.element(i))
            );
        }

        let grand_product_evals = GrandProductArgument::instantiate_argument(
            &q_last,
            &q_blind,
            &agg_poly,
            &permutation_oracles,
            &witness_oracles,
            &deltas,
            beta,
            gamma,
            &domain,
            &extended_coset_domain,
        );

        let grand_product_poly = DensePolynomial::<F>::from_coefficients_slice(
            &extended_coset_domain.coset_ifft(&grand_product_evals),
        );

        let q = &grand_product_poly / &domain.vanishing_polynomial().into();
        assert_eq!(
            grand_product_poly,
            &q * &domain.vanishing_polynomial().into()
        );

        let evaluation_challenge = F::rand(&mut rng);
        let q_eval = q.evaluate(&evaluation_challenge);

        // Actually we must construct verifier oracles and evaluate query set, but for this test it's not needed
        let opening = GrandProductArgument::open_argument(
            &q_last,
            &q_blind,
            &agg_poly,
            &permutation_oracles,
            &witness_oracles,
            &deltas,
            beta,
            gamma,
            &domain,
            evaluation_challenge,
        );

        assert_eq!(opening, q_eval * domain.vanishing_polynomial().evaluate(&evaluation_challenge));
    }
}
