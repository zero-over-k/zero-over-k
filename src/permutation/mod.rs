use std::marker::PhantomData;

use ark_ff::PrimeField;
use ark_poly::{
    univariate::DensePolynomial, EvaluationDomain, GeneralEvaluationDomain,
    Polynomial,
};
use ark_std::rand::RngCore;
use itertools::Itertools;

use crate::{
    commitment::HomomorphicCommitment,
    oracles::{
        fixed::FixedOracle,
        query::QueryContext,
        rotation::{Rotation, Sign},
        traits::{ConcreteOracle, Instantiable, WitnessOracle},
        witness::WitnessProverOracle,
    },
    permutation::grand_product::GrandProductArgument,
};

pub mod grand_product;
mod playground;

pub struct PermutationArgument<F: PrimeField, PC: HomomorphicCommitment<F>> {
    m: usize, // max number of columns that can be included per single grand product argument such that it does not exceed quotient degree
    u: usize, // number of usable rows
    _f: PhantomData<F>,
    _pc: PhantomData<PC>,
}

impl<F: PrimeField, PC: HomomorphicCommitment<F>> PermutationArgument<F, PC> {
    /*
        Note that (1 - (q_last + q_blind)) * (Z(wX) * permutation_part - Z(x) * identity_part)) has two symmetrical parts that affect degree in same time
        So as baseline we have multiplication of let's say q_last * Z(wX) which gives degree 2n - 2 so after division with zH(X) we have 2n - 2 - n = n - 2
        With every new oracle added degree increases for n - 1:
        1 oracle -> n - 2 + n - 1 = 2n - 3: 2n domain size
        2 oracles -> n - 2 + 2n - 2 = 3n - 4: 4n domain size
        3 oracles ->  n - 2 + 3n - 3 = 4n - 5: 4n domain size
        4 oracles -> n - 2 + 4n - 4 = 5n - 6: 8n domain size

        So, minimal domain to use when permutation is enabled will be 2n
    */

    pub fn new(scaling_factor: usize, u: usize) -> Self {
        // extended coset domain is defined as Domain of size original_domain_size * scaling_factor, where minimal scaling factor,
        // as noted above, is 2
        let m = scaling_factor - 1;
        Self {
            m,
            u,
            _f: PhantomData,
            _pc: PhantomData,
        }
    }

    pub fn construct_agg_polys<R: RngCore>(
        &self,
        witness_oracles: &[WitnessProverOracle<F>], // Only oracles that are included in permutation
        permutation_oracles: &[FixedOracle<F, PC>],
        deltas: &[F],
        beta: F,
        gamma: F,
        domain: &GeneralEvaluationDomain<F>,
        extended_coset_domain: &GeneralEvaluationDomain<F>,
        zk_rng: &mut R,
    ) -> Vec<WitnessProverOracle<F>> {
        assert_eq!(witness_oracles.len(), permutation_oracles.len());
        assert_eq!(witness_oracles.len(), deltas.len());

        let oracle_chunks = witness_oracles.chunks(self.m);
        let sigma_chunks = permutation_oracles.chunks(self.m);
        let delta_chunks = deltas.chunks(self.m);

        let mut agg_polys =
            Vec::<WitnessProverOracle<F>>::with_capacity(oracle_chunks.len());

        for (i, ((ws, sigmas), ds)) in oracle_chunks
            .zip(sigma_chunks)
            .zip(delta_chunks)
            .enumerate()
        {
            let init_value = if i == 0 {
                F::one()
            } else {
                agg_polys[i - 1].get_evals()[self.u]
            };

            let agg_i = GrandProductArgument::construct_agg_poly(
                i,
                init_value,
                sigmas,
                ws,
                ds,
                beta,
                gamma,
                self.u,
                domain,
                extended_coset_domain,
                zk_rng,
            );

            agg_polys.push(agg_i);
        }

        // sanity
        let z_last_evals = domain.fft(agg_polys.last().unwrap().polynomial());
        assert_eq!(z_last_evals[self.u], F::one());

        agg_polys
    }

    /*
        Construct in order:
        1. z_agg[first][0] = 1
        2. all grand product arguments
        3. all stitches z_agg[i-1][u] = z_agg_[i][0]
        4. z_agg[u] = 0/1
    */
    pub fn instantiate_argument_at_omega_i(
        &self,
        l_0_coset_evals: &Vec<F>, // lagrange poly should not be fixed column, it's not committed since it can be evaluated in O(log(N))
        q_last_coset_evals: &Vec<F>, // q_last is 1 only at index u, so it can also be treated as Lu(X)
        q_blind: &FixedOracle<F, PC>,
        witness_oracles: &[WitnessProverOracle<F>], // Only oracles that are included in permutation
        permutation_oracles: &[FixedOracle<F, PC>],
        agg_polys: &[WitnessProverOracle<F>],
        omega_index: usize,
        omega: F,
        deltas: &[F],
        beta: F,
        gamma: F,
        domain: &GeneralEvaluationDomain<F>,
        alpha_powers: &[F], // quotient separation challenges
    ) -> F {
        assert_eq!(witness_oracles.len(), permutation_oracles.len());
        assert_eq!(witness_oracles.len(), deltas.len());

        let oracle_chunks = witness_oracles.chunks(self.m);
        let sigma_chunks = permutation_oracles.chunks(self.m);
        let delta_chunks = deltas.chunks(self.m);

        assert_eq!(oracle_chunks.len(), sigma_chunks.len());
        assert_eq!(oracle_chunks.len(), delta_chunks.len());
        assert_eq!(agg_polys.len(), oracle_chunks.len());

        /*
            alphas len should be:
            + 1: for z_agg[first][0] = 1,
            + 1:  for z_agg[last][u] = 0/1
            + agg_polys_len - 1: for z_agg[i-1][u] = z_agg_[i][0] stitch between (i-1, i)
            + agg_polys_len: for checking that each grand product chunks is correct
        */
        let expected_alphas_len = 2 * agg_polys.len() + 1 + 1 - 1;
        assert_eq!(expected_alphas_len, alpha_powers.len());

        let ctx = QueryContext::<F>::ExtendedCoset(
            domain.size(),
            Rotation::curr(),
            omega_index,
        );
        let domain_size = domain.size();

        let mut permutation_eval = alpha_powers[0]
            * l_0_coset_evals[omega_index]
            * (F::one() - agg_polys[0].query(&ctx));
        let mut alpha_shift = 1;

        // // let mut permutation_eval = F::zero();
        for (i, ((ws, sigmas), ds)) in oracle_chunks
            .zip(sigma_chunks)
            .zip(delta_chunks)
            .enumerate()
        {
            permutation_eval += alpha_powers[i + alpha_shift]
                * GrandProductArgument::instantiate_argument_at_omega_i(
                    q_last_coset_evals,
                    q_blind,
                    &agg_polys[i],
                    sigmas,
                    ws,
                    ds,
                    beta,
                    gamma,
                    domain_size,
                    omega,
                    omega_index,
                );
        }

        alpha_shift += agg_polys.len();

        let shifted_ctx = QueryContext::<F>::ExtendedCoset(
            domain.size(),
            Rotation::new(self.u, Sign::Plus),
            omega_index,
        );
        for i in 0..agg_polys.len() - 1 {
            permutation_eval += alpha_powers[i + alpha_shift]
                * l_0_coset_evals[omega_index]
                * (agg_polys[i + 1].query(&ctx)
                    - agg_polys[i].query(&shifted_ctx));
        }

        let z_last_eval = agg_polys.last().unwrap().query(&ctx);
        permutation_eval += alpha_powers.last().unwrap().clone()
            * q_last_coset_evals[omega_index]
            * (z_last_eval * z_last_eval - z_last_eval);

        permutation_eval
    }

    pub fn open_argument(
        &self,
        l_0_eval: F,
        q_last_eval: F,
        q_blind: &FixedOracle<F, PC>,
        agg_polys: &[impl WitnessOracle<F>], // TODO: make this verifier concrete oracle
        permutation_oracles: &[FixedOracle<F, PC>],
        witness_oracles: &[impl WitnessOracle<F>], // TODO: make this verifier concrete oracle
        deltas: &[F],
        beta: F,
        gamma: F,
        domain: &GeneralEvaluationDomain<F>,
        evaluation_challenge: F,
        alpha_powers: &[F], // quotient separation challenges
    ) -> F {
        assert_eq!(witness_oracles.len(), permutation_oracles.len());
        assert_eq!(witness_oracles.len(), deltas.len());

        let oracle_chunks = witness_oracles.chunks(self.m);
        let sigma_chunks = permutation_oracles.chunks(self.m);
        let delta_chunks = deltas.chunks(self.m);

        assert_eq!(oracle_chunks.len(), sigma_chunks.len());
        assert_eq!(oracle_chunks.len(), delta_chunks.len());
        assert_eq!(agg_polys.len(), oracle_chunks.len());

        /*
            alphas len should be:
            + 1: for z_agg[first][0] = 1,
            + 1:  for z_agg[last][u] = 0/1
            + agg_polys_len - 1: for z_agg[i-1][u] = z_agg_[i][0] stitch between (i-1, i)
            + agg_polys_len: for checking that each grand product chunks is correct
        */
        let expected_alphas_len = 2 * agg_polys.len() + 1 + 1 - 1;
        assert_eq!(expected_alphas_len, alpha_powers.len());

        let ctx = QueryContext::<F>::Challenge(evaluation_challenge);
        let mut permutation_eval =
            alpha_powers[0] * l_0_eval * (F::one() - agg_polys[0].query(&ctx));
        let mut alpha_shift = 1;

        // //let mut permutation_eval = F::zero();
        for (i, ((ws, sigmas), ds)) in oracle_chunks
            .zip(sigma_chunks)
            .zip(delta_chunks)
            .enumerate()
        {
            permutation_eval += alpha_powers[i + alpha_shift]
                * GrandProductArgument::open_argument(
                    q_last_eval,
                    q_blind,
                    &agg_polys[i],
                    sigmas,
                    ws,
                    ds,
                    beta,
                    gamma,
                    domain,
                    evaluation_challenge,
                );
        }

        alpha_shift += agg_polys.len();

        let shifted_ctx = QueryContext::<F>::Challenge(
            domain.element(self.u) * evaluation_challenge,
        );
        for i in 0..agg_polys.len() - 1 {
            permutation_eval += alpha_powers[i + alpha_shift]
                * l_0_eval
                * (agg_polys[i + 1].query(&ctx)
                    - agg_polys[i].query(&shifted_ctx));
        }

        let z_last_eval = agg_polys.last().unwrap().query(&ctx);
        permutation_eval += alpha_powers.last().unwrap().clone()
            * q_last_eval
            * (z_last_eval * z_last_eval - z_last_eval);

        permutation_eval
    }
}

#[cfg(test)]
mod test {
    use super::PermutationArgument;

    use std::{
        collections::{BTreeMap, BTreeSet},
        iter::successors,
    };

    use crate::{
        commitment::KZG10,
        oracles::{
            fixed::FixedOracle, rotation::Rotation, traits::Instantiable,
            witness::WitnessProverOracle,
        },
        permutation,
        util::compute_vanishing_poly_over_coset,
    };
    use ark_ff::{FftField, Field, One, UniformRand, Zero};
    use ark_poly::{
        univariate::DensePolynomial, EvaluationDomain, GeneralEvaluationDomain,
        Polynomial, UVPolynomial,
    };

    use ark_bls12_381::{Bls12_381, Fr as F};
    use ark_std::test_rng;

    type PC = KZG10<Bls12_381>;

    #[test]
    fn test_chunked_permutation() {
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

        // For scaling factor 2 we will have 2 chunks
        let scaling_factor = 2;
        let extended_coset_domain =
            GeneralEvaluationDomain::<F>::new(scaling_factor * domain_size)
                .unwrap();

        let a = WitnessProverOracle {
            label: "a".to_string(),
            poly: a.clone(),
            evals_at_coset_of_extended_domain: Some(
                extended_coset_domain.coset_fft(&a),
            ),
            queried_rotations: BTreeSet::from([Rotation::curr()]),
            should_permute: true,
            evals: Some(a_evals),
        };

        let b = WitnessProverOracle {
            label: "b".to_string(),
            poly: b.clone(),
            evals_at_coset_of_extended_domain: Some(
                extended_coset_domain.coset_fft(&b),
            ),
            queried_rotations: BTreeSet::from([Rotation::curr()]),
            should_permute: true,
            evals: Some(b_evals),
        };

        let sigma_1 = FixedOracle::<F, PC> {
            label: "sigma_1".to_string(),
            poly: sigma_1.clone(),
            evals_at_coset_of_extended_domain: Some(
                extended_coset_domain.coset_fft(&sigma_1),
            ),
            evals: Some(sigma_1_evals),
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
            evals: Some(sigma_2_evals),
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
            evals: None,
            queried_rotations: BTreeSet::from([Rotation::curr()]),
            evals_at_challenges: BTreeMap::default(),
            commitment: None,
        };

        let witness_oracles = [a, b];
        let permutation_oracles = [sigma_1, sigma_2];

        let deltas = [F::one(), F::from(13u64)];

        let beta = F::rand(&mut rng);
        let gamma = F::rand(&mut rng);

        let permutation_argument =
            PermutationArgument::<F, PC>::new(scaling_factor, u);

        let z_polys = permutation_argument.construct_agg_polys(
            &witness_oracles,
            &permutation_oracles,
            &deltas,
            beta,
            gamma,
            &domain,
            &extended_coset_domain,
            &mut rng,
        );

        let mut l_0_evals = vec![F::zero(); domain.size()];
        l_0_evals[0] = F::one();
        let l0 =
            DensePolynomial::from_coefficients_slice(&domain.ifft(&l_0_evals));
        let l_0_coset_evals = extended_coset_domain.coset_fft(&l0);

        let lu = DensePolynomial::from_coefficients_slice(
            &domain.ifft(&q_last_evals),
        );
        let l_u_coset_evals = extended_coset_domain.coset_fft(&lu);

        let expected_alphas_len = 2 * z_polys.len() + 1 + 1 - 1;
        let alpha = F::rand(&mut rng);
        let powers_of_alpha: Vec<F> =
            successors(Some(F::one()), |alpha_i| Some(*alpha_i * alpha))
                .take(expected_alphas_len)
                .collect();

        let mut permutation_coset_evals =
            Vec::<F>::with_capacity(extended_coset_domain.size());
        for i in 0..extended_coset_domain.size() {
            let pe = permutation_argument.instantiate_argument_at_omega_i(
                &l_0_coset_evals,
                &l_u_coset_evals,
                &q_blind,
                &witness_oracles,
                &permutation_oracles,
                &z_polys,
                i,
                extended_coset_domain.element(i),
                &deltas,
                beta,
                gamma,
                &domain,
                &powers_of_alpha,
            );

            permutation_coset_evals.push(pe);
        }

        let mut zh_evals = compute_vanishing_poly_over_coset(
            extended_coset_domain,
            domain_size as u64,
        );
        ark_ff::batch_inversion(&mut zh_evals);

        let quotient_evals = permutation_coset_evals
            .iter()
            .zip(zh_evals.iter())
            .map(|(&pi, &zhi)| pi * zhi)
            .collect::<Vec<F>>();

        let quotient = DensePolynomial::from_coefficients_slice(
            &extended_coset_domain.coset_ifft(&quotient_evals),
        );

        let evaluation_challenge = F::rand(&mut rng);

        let q_eval = quotient.evaluate(&evaluation_challenge);
        let zh_eval = domain
            .vanishing_polynomial()
            .evaluate(&evaluation_challenge);

        let l_0_eval = l0.evaluate(&evaluation_challenge);
        let l_u_eval = lu.evaluate(&evaluation_challenge);

        let permutation_eval = permutation_argument.open_argument(
            l_0_eval,
            l_u_eval,
            &q_blind,
            &z_polys,
            &permutation_oracles,
            &witness_oracles,
            &deltas,
            beta,
            gamma,
            &domain,
            evaluation_challenge,
            &powers_of_alpha,
        );

        assert_eq!(permutation_eval, q_eval * zh_eval);
    }
}
