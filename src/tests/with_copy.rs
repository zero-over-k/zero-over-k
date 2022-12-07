#[cfg(test)]
mod copy_constraint_tests {
    use std::{
        collections::{BTreeMap, BTreeSet},
        iter::successors,
    };

    use ark_ff::{Field, One, UniformRand, Zero};
    use ark_poly::{
        univariate::DensePolynomial, EvaluationDomain, GeneralEvaluationDomain,
        Polynomial, UVPolynomial,
    };
    use ark_poly_commit::{LabeledPolynomial, PolynomialCommitment};
    use ark_std::test_rng;
    use rand_chacha::ChaChaRng;

    use crate::{
        commitment::KZG10,
        data_structures::{
            PermutationInfo, ProverKey, ProverPreprocessedInput,
            VerifierPreprocessedInput,
        },
        indexer::Indexer,
        oracles::{
            fixed::FixedVerifierOracle,
            instance::{InstanceProverOracle, InstanceVerifierOracle},
            rotation::Sign,
            traits::Instantiable,
            witness::WitnessVerifierOracle,
        },
        rng::SimpleHashFiatShamirRng,
        util::compute_vanishing_poly_over_coset,
        vo::{
            generic_vo::GenericVO,
            precompiled::{plonk_arith::PrecompiledPlonkArith, PrecompiledVO},
            VirtualOracle,
        },
    };
    use ark_bls12_381::{Bls12_381, Fr as F};

    type PC = KZG10<Bls12_381>;

    use crate::PIL;
    use blake2::Blake2s;

    type FS = SimpleHashFiatShamirRng<Blake2s, ChaChaRng>;

    type PilInstance = PIL<F, PC, FS>;

    use crate::{
        oracles::{
            fixed::FixedProverOracle, rotation::Rotation,
            witness::WitnessProverOracle,
        },
        permutation::PermutationArgument,
    };
    #[test]
    fn copy_simple() {
        /*
            We encode circuit x^3 + 2x + 12 = 0, (solution x = -2, -2 ^3 + 2*(-2) + 12 = -8 - 4 + 12 = 0)

            gate0: a0 * b0 = c0 |==> x * x = x^2
            gate1: a1 * b1 = c1 |==> x^2 * x = x^3
            gate2: b2 = PI[2]   |==> b2 = 2
            gate3: a3 * b3 = c3 |==> 2x = 2 * x
            gate4: a4 + b4 = c4 |==> x^3 + 2x
            gate5: b5 = PI[5]   |==> b5 = 12
            gate6: a5 + b5 = c5 |==> x3 + 2x + 12
            gate7: c5 = PI[5]   |==> c5 == 0


            * -> can be whatever

            row        a       b      c         PI

            0          x       x      x^2       0     copy: a0 = b0

            1          x^2     x      x^3       0     copy: a1 = c0, b1 = a0

            2          *       2       *        2     copy:

            3          x       2       2x       0     copy: a3 = a0, b2 = b3

            4          x^3     2x     x^3+2x    0     copy: a4 = c1, b4 = c3

            5           *      12       *       12     copy:

            6         x^3+2x   12     x^3+2x+12  0     copy: a6 = c4, b5 = b6

            7           *       *     x^3+2x+12  0     copy  c6 = c7


            a_evals = [x, x^2, dummy, x, x^3, dummy, x^3 + 2x, dummy, blinds...]

            b_evals = [x, x, 2, 2, 2x, 12, 12, dummy, blinds...]

            c_evals = [x^2, x^3, dummy, 2x, x^3 + 2x, dummy, x^3+2x+12, x^3+2x+12, blinds...]


            cycles:
                (a0, b0, b1, a3) (a1, c0) (b2, b3) (a4, c1) (b4, c3) (a6, c4) (b5, b6) (c6, c7)


            Begin NOTE:
            When we use permutation we need one more element to encode full accumulation in z(X)
            consider simple example without rotations:
            a =  [a0, a1, a2]
            b =  [b0, b1, b2]

            a, b both can fit in domain of k = 4, 3 evals + 1 blinding

            But:
            z =  [1, a0/b0, a0a1/b0b1, a0a1a2/b0b1b2] + 2 random elements for blinding because z(X) is being opened in x and wx
            END Note:

            Our polynomials can fit in k = 8, 7 evals + 1 blinding but because of the above mentioned problem we have to work in domain of k = 16

            Usable rows are: u = 8 (because z(X) needs one more eval)
            we an use rest of rows to blind

            q_last =  [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
            q_blind = [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1]
        */

        let mut rng = test_rng();
        let domain_size = 16;

        let fill_zeroes = |evals: &mut Vec<F>| {
            let zeroes = vec![F::zero(); domain_size - evals.len()];
            evals.extend_from_slice(&zeroes);
        };

        let fill_blinds = |evals: &mut Vec<F>| {
            let mut rng = test_rng();
            let blinds = vec![F::rand(&mut rng); domain_size - evals.len()];
            evals.extend_from_slice(&blinds);
        };

        let domain_size = 16;
        let poly_degree = domain_size - 1;
        let _max_degree = poly_degree;

        let domain = GeneralEvaluationDomain::<F>::new(domain_size).unwrap();

        let x = -F::from(2u64);
        let x_squared = x * x;
        let x_cube = x * x_squared;

        let two = F::from(2u64);
        let two_x = two * x;

        let twelve = F::from(12u64);

        let zero = F::zero();
        let one = F::one();

        let dummy = F::from(999u64);

        let fill_dummy = |evals: &mut Vec<F>| {
            let dummys = vec![dummy.clone(); domain_size - evals.len()];
            evals.extend_from_slice(&dummys);
        };

        let mut a_evals =
            vec![x, x_squared, dummy, x, x_cube, dummy, x_cube + two_x, dummy];

        let mut b_evals = vec![x, x, two, two, two_x, twelve, twelve, dummy];

        let mut c_evals = vec![
            x_squared,
            x_cube,
            dummy,
            two_x,
            x_cube + two_x,
            dummy,
            x_cube + two_x + twelve,
            x_cube + two_x + twelve,
        ];

        let mut pi_evals =
            vec![zero, zero, two, zero, zero, twelve, zero, zero];

        let mut qm_evals = vec![one, one, zero, one, zero, zero, zero, zero];

        let mut ql_evals = vec![zero, zero, zero, zero, one, zero, one, zero];

        let mut qr_evals = vec![zero, zero, -one, zero, one, -one, one, zero];

        let mut qo_evals = vec![-one, -one, zero, -one, -one, zero, -one, -one];

        assert_eq!(x_cube + two_x + twelve, zero);

        fill_zeroes(&mut pi_evals);
        fill_zeroes(&mut qm_evals);
        fill_zeroes(&mut ql_evals);
        fill_zeroes(&mut qr_evals);
        fill_zeroes(&mut qo_evals);

        fill_blinds(&mut a_evals);
        fill_blinds(&mut b_evals);
        fill_blinds(&mut c_evals);

        // Here we check that circuit is satisfiable
        for i in 0..domain.size() {
            let arith = qm_evals[i] * a_evals[i] * b_evals[i]
                + ql_evals[i] * a_evals[i]
                + qr_evals[i] * b_evals[i]
                + qo_evals[i] * c_evals[i]
                + pi_evals[i];

            assert_eq!(arith, F::zero());
        }

        let deltas = [one, F::from(7u64), F::from(13u64)];

        // cycles:
        // (a0, b0, b1, a3) (b2, b3) (b5, b6) (c6, c7) (a1, c0) (a4, c1) (a6, c4) (b4, c3)

        // skip for now

        /*
            a0 -> b0
            a1 -> c0
            a2 -> a2
            a3 -> a0
            a4 -> c1
            a5 -> a5
            a6 -> c4
            a7 -> a7
            ...fill dummys
        */

        let mut sigma_1_evals = vec![
            deltas[1] * domain.element(0), //0
            deltas[2] * domain.element(0), //1
            deltas[0] * domain.element(2), //2
            deltas[0] * domain.element(0), //3
            deltas[2] * domain.element(1), //4
            deltas[0] * domain.element(5), //5
            deltas[2] * domain.element(4), //6
            deltas[0] * domain.element(7), //7
        ];

        fill_dummy(&mut sigma_1_evals);

        // cycles:
        // (a0, b0, b1, a3) (b2, b3) (b5, b6) (c6, c7) (a1, c0) (a4, c1) (a6, c4) (b4, c3)

        // skip for now

        /*
            b0 -> b1
            b1 -> a3
            b2 -> b3
            b3 -> b2
            b4 -> c3
            b5 -> b6
            b6 -> b5
            b7 -> b7
            ...fill dummys
        */

        let mut sigma_2_evals = vec![
            deltas[1] * domain.element(1), //0
            deltas[0] * domain.element(3), //1
            deltas[1] * domain.element(3), //2
            deltas[1] * domain.element(2), //3
            deltas[2] * domain.element(3), //4
            deltas[1] * domain.element(6), //5
            deltas[1] * domain.element(5), //6
            deltas[1] * domain.element(7), //7
        ];

        fill_dummy(&mut sigma_2_evals);

        // cycles:
        // (a0, b0, b1, a3) (b2, b3) (b5, b6) (c6, c7) (a1, c0) (a4, c1) (a6, c4) (b4, c3)

        // skip for now
        /*
            c0 -> a1
            c1 -> a4
            c2 -> c2
            c3 -> b4
            c4 -> a6
            c5 -> c5
            c6 -> c7
            c7 -> c6
            ...fill dummys
        */

        let mut sigma_3_evals = vec![
            deltas[0] * domain.element(1), //0
            deltas[0] * domain.element(4), //1
            deltas[2] * domain.element(2), //2
            deltas[1] * domain.element(4), //3
            deltas[0] * domain.element(6), //4
            deltas[2] * domain.element(5), //5
            deltas[2] * domain.element(7), //6
            deltas[2] * domain.element(6), //7
        ];

        fill_dummy(&mut sigma_3_evals);

        // assert_eq!(c_evals[6] * sigma_3_evals[6], c_evals[7]  * sigma_3_evals[7]);

        // println!("Surv")

        let u = 8; // see Note at comment on top
        let beta = F::rand(&mut rng);
        let gamma = F::rand(&mut rng);

        let mut z_evals = vec![];
        let mut z_prev = F::one();
        z_evals.push(z_prev);

        let omegas: Vec<F> = domain.elements().collect();

        for i in 0..u {
            let nom_a = a_evals[i] + beta * deltas[0] * omegas[i] + gamma;
            let nom_b = b_evals[i] + beta * deltas[1] * omegas[i] + gamma;
            let nom_c = c_evals[i] + beta * deltas[2] * omegas[i] + gamma;

            let denom_a = a_evals[i] + beta * sigma_1_evals[i] + gamma;
            let denom_b = b_evals[i] + beta * sigma_2_evals[i] + gamma;
            let denom_c = c_evals[i] + beta * sigma_3_evals[i] + gamma;

            let nom = nom_a * nom_b * nom_c;
            let denom = denom_a * denom_b * denom_c;

            z_prev *= nom * denom.inverse().unwrap();
            z_evals.push(z_prev);
        }

        assert_eq!(z_evals[u], F::one());

        fill_dummy(&mut z_evals);

        let a_poly =
            DensePolynomial::from_coefficients_slice(&domain.ifft(&a_evals));
        let b_poly =
            DensePolynomial::from_coefficients_slice(&domain.ifft(&b_evals));
        let c_poly =
            DensePolynomial::from_coefficients_slice(&domain.ifft(&c_evals));

        let _pi_poly =
            DensePolynomial::from_coefficients_slice(&domain.ifft(&pi_evals));

        let _qm_poly =
            DensePolynomial::from_coefficients_slice(&domain.ifft(&qm_evals));
        let _ql_poly =
            DensePolynomial::from_coefficients_slice(&domain.ifft(&ql_evals));
        let _qr_poly =
            DensePolynomial::from_coefficients_slice(&domain.ifft(&qr_evals));

        let _qo_poly =
            DensePolynomial::from_coefficients_slice(&domain.ifft(&qo_evals));

        let sigma_1_poly = DensePolynomial::from_coefficients_slice(
            &domain.ifft(&sigma_1_evals),
        );
        let sigma_2_poly = DensePolynomial::from_coefficients_slice(
            &domain.ifft(&sigma_2_evals),
        );
        let sigma_3_poly = DensePolynomial::from_coefficients_slice(
            &domain.ifft(&sigma_3_evals),
        );

        // Test full permutation argument with chunking
        // We have qm * a * b as biggest term => 3 * (n - 1) - n = 2n - 3, so we can work in 2n

        let scaling_factor = 2;

        let extended_coset_domain =
            GeneralEvaluationDomain::<F>::new(scaling_factor * domain_size)
                .unwrap();

        let mut a = WitnessProverOracle {
            label: "a".to_string(),
            poly: a_poly.clone(),
            evals_at_coset_of_extended_domain: Some(
                extended_coset_domain.coset_fft(&a_poly),
            ),
            queried_rotations: BTreeSet::from([Rotation::curr()]),
            should_permute: true,
            evals: a_evals,
        };

        let mut b = WitnessProverOracle {
            label: "b".to_string(),
            poly: b_poly.clone(),
            evals_at_coset_of_extended_domain: Some(
                extended_coset_domain.coset_fft(&b_poly),
            ),
            queried_rotations: BTreeSet::from([Rotation::curr()]),
            should_permute: true,
            evals: b_evals,
        };

        let mut c = WitnessProverOracle {
            label: "c".to_string(),
            poly: c_poly.clone(),
            evals_at_coset_of_extended_domain: Some(
                extended_coset_domain.coset_fft(&c_poly),
            ),
            queried_rotations: BTreeSet::from([Rotation::curr()]),
            should_permute: true,
            evals: c_evals,
        };

        let sigma1 = FixedProverOracle {
            label: "sigma_1".to_string(),
            poly: sigma_1_poly.clone(),
            evals_at_coset_of_extended_domain: Some(
                extended_coset_domain.coset_fft(&sigma_1_poly),
            ),
            evals: sigma_1_evals,
            queried_rotations: BTreeSet::from([Rotation::curr()]),
        };

        let sigma2 = FixedProverOracle {
            label: "sigma_2".to_string(),
            poly: sigma_2_poly.clone(),
            evals_at_coset_of_extended_domain: Some(
                extended_coset_domain.coset_fft(&sigma_2_poly),
            ),
            evals: sigma_2_evals,
            queried_rotations: BTreeSet::from([Rotation::curr()]),
        };

        let sigma3 = FixedProverOracle {
            label: "sigma_3".to_string(),
            poly: sigma_3_poly.clone(),
            evals_at_coset_of_extended_domain: Some(
                extended_coset_domain.coset_fft(&sigma_3_poly),
            ),
            evals: sigma_3_evals,
            queried_rotations: BTreeSet::from([Rotation::curr()]),
        };

        let perm_params = PermutationInfo {
            u: 8, // see Note at comment on top
            deltas: deltas.to_vec(),
        };
        let permutation_argument =
            PermutationArgument::<F>::new(scaling_factor, &perm_params);

        let witness_oracles: &mut [&mut WitnessProverOracle<F>] = &mut [&mut a, &mut b, &mut c];
        let permutation_oracles = [sigma1, sigma2, sigma3];

        let mut oracles_to_copy: Vec<&WitnessProverOracle<F>> = Vec::with_capacity(witness_oracles.len());
        let mut w: Vec<&WitnessProverOracle<F>> = Vec::with_capacity(witness_oracles.len());
        for o in witness_oracles.iter() {
            if o.should_permute {
                oracles_to_copy.push(o);
            }
            w.push(o as &WitnessProverOracle<F>);
        }

        let agg_polys = permutation_argument.construct_agg_polys(
            oracles_to_copy.as_slice(),
            &permutation_oracles,
            beta,
            gamma,
            &domain,
            &extended_coset_domain,
            &mut rng,
        );

        let mut l0_evals = vec![F::zero(); domain_size];
        l0_evals[0] = F::one();
        let l0 =
            DensePolynomial::from_coefficients_slice(&domain.ifft(&l0_evals));
        let l0_coset_evals = extended_coset_domain.coset_fft(&l0);

        let mut lu_evals = vec![F::zero(); domain_size];
        lu_evals[u] = F::one();
        let lu =
            DensePolynomial::from_coefficients_slice(&domain.ifft(&lu_evals));
        let lu_coset_evals = extended_coset_domain.coset_fft(&lu);

        let mut q_blind_evals = vec![F::one(); domain.size()];
        for i in 0..=u {
            q_blind_evals[i] = F::zero();
        }

        let q_blind_poly = DensePolynomial::<F>::from_coefficients_slice(
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

        /*
            alphas len should be:
            + 1: for z_agg[first][0] = 1,
            + 1:  for z_agg[last][u] = 0/1
            + agg_polys_len - 1: for z_agg[i-1][u] = z_agg_[i][0] stitch between (i-1, i)
            + agg_polys_len: for checking that each grand product chunks is correct
        */
        let expected_alphas_len = 2 * agg_polys.len() + 1 + 1 - 1;
        let alpha = F::rand(&mut rng);
        let powers_of_alpha: Vec<F> =
            successors(Some(F::one()), |alpha_i| Some(*alpha_i * alpha))
                .take(expected_alphas_len)
                .collect();

        let mut permutation_coset_evals =
            Vec::<F>::with_capacity(extended_coset_domain.size());
        for i in 0..extended_coset_domain.size() {
            let q_i = permutation_argument.instantiate_argument_at_omega_i(
                &l0_coset_evals,
                &lu_coset_evals,
                &q_blind,
                witness_oracles
                    .iter()
                    .map(|x| x as &WitnessProverOracle<F>)
                    .collect::<Vec<&WitnessProverOracle<F>>>()
                    .as_slice(),
                &permutation_oracles,
                &agg_polys,
                i,
                extended_coset_domain.element(i),
                beta,
                gamma,
                &domain,
                &powers_of_alpha,
            ).unwrap();

            permutation_coset_evals.push(q_i);
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

        let q_blind = FixedVerifierOracle::<F, PC> {
            label: "q_blind".into(),
            queried_rotations: BTreeSet::from([Rotation::curr()]),
            evals_at_challenges: BTreeMap::from([(
                evaluation_challenge,
                q_blind_poly.evaluate(&evaluation_challenge),
            )]),
            commitment: None,
        };

        let a = WitnessVerifierOracle::<F, PC> {
            label: "a".to_string(),
            queried_rotations: BTreeSet::from([Rotation::curr()]),
            evals_at_challenges: BTreeMap::from([(
                evaluation_challenge,
                a_poly.evaluate(&evaluation_challenge),
            )]),
            commitment: None,
            should_permute: true,
        };

        let b = WitnessVerifierOracle::<F, PC> {
            label: "b".to_string(),
            queried_rotations: BTreeSet::from([Rotation::curr()]),
            evals_at_challenges: BTreeMap::from([(
                evaluation_challenge,
                b_poly.evaluate(&evaluation_challenge),
            )]),
            commitment: None,
            should_permute: true,
        };

        let c = WitnessVerifierOracle::<F, PC> {
            label: "c".to_string(),
            queried_rotations: BTreeSet::from([Rotation::curr()]),
            evals_at_challenges: BTreeMap::from([(
                evaluation_challenge,
                c_poly.evaluate(&evaluation_challenge),
            )]),
            commitment: None,
            should_permute: true,
        };

        let sigma_1 = FixedVerifierOracle::<F, PC> {
            label: "sigma_1".into(),
            queried_rotations: BTreeSet::from([Rotation::curr()]),
            evals_at_challenges: BTreeMap::from([(
                evaluation_challenge,
                sigma_1_poly.evaluate(&evaluation_challenge),
            )]),
            commitment: None,
        };

        let sigma_2 = FixedVerifierOracle::<F, PC> {
            label: "sigma_2".into(),
            queried_rotations: BTreeSet::from([Rotation::curr()]),
            evals_at_challenges: BTreeMap::from([(
                evaluation_challenge,
                sigma_2_poly.evaluate(&evaluation_challenge),
            )]),
            commitment: None,
        };

        let sigma_3 = FixedVerifierOracle::<F, PC> {
            label: "sigma_3".into(),
            queried_rotations: BTreeSet::from([Rotation::curr()]),
            evals_at_challenges: BTreeMap::from([(
                evaluation_challenge,
                sigma_3_poly.evaluate(&evaluation_challenge),
            )]),
            commitment: None,
        };

        let z_poly_0 = WitnessVerifierOracle::<F, PC> {
            label: "agg_poly_0".to_string(),
            queried_rotations: BTreeSet::from([
                Rotation::curr(),
                Rotation::next(),
                Rotation::new(u, Sign::Plus),
            ]),
            evals_at_challenges: BTreeMap::from([
                (
                    evaluation_challenge,
                    agg_polys[0].polynomial().evaluate(&evaluation_challenge),
                ),
                (
                    evaluation_challenge * domain.element(1),
                    agg_polys[0]
                        .polynomial()
                        .evaluate(&(domain.element(1) * evaluation_challenge)),
                ),
                (
                    evaluation_challenge * domain.element(u),
                    agg_polys[0]
                        .polynomial()
                        .evaluate(&(domain.element(u) * evaluation_challenge)),
                ),
            ]),
            commitment: None,
            should_permute: false,
        };

        let z_poly_1 = WitnessVerifierOracle::<F, PC> {
            label: "agg_poly_1".to_string(),
            queried_rotations: BTreeSet::from([
                Rotation::curr(),
                Rotation::next(),
                Rotation::new(u, Sign::Plus),
            ]),
            evals_at_challenges: BTreeMap::from([
                (
                    evaluation_challenge,
                    agg_polys[1].polynomial().evaluate(&evaluation_challenge),
                ),
                (
                    evaluation_challenge * domain.element(1),
                    agg_polys[1]
                        .polynomial()
                        .evaluate(&(domain.element(1) * evaluation_challenge)),
                ),
                (
                    evaluation_challenge * domain.element(u),
                    agg_polys[1]
                        .polynomial()
                        .evaluate(&(domain.element(u) * evaluation_challenge)),
                ),
            ]),
            commitment: None,
            should_permute: false,
        };

        let z_poly_2 = WitnessVerifierOracle::<F, PC> {
            label: "agg_poly_2".to_string(),
            queried_rotations: BTreeSet::from([
                Rotation::curr(),
                Rotation::next(),
            ]),
            evals_at_challenges: BTreeMap::from([
                (
                    evaluation_challenge,
                    agg_polys[2].polynomial().evaluate(&evaluation_challenge),
                ),
                (
                    evaluation_challenge * domain.element(1),
                    agg_polys[2]
                        .polynomial()
                        .evaluate(&(domain.element(1) * evaluation_challenge)),
                ),
            ]),
            commitment: None,
            should_permute: false,
        };

        let witness_oracles = [&a, &b, &c];
        let permutation_oracles = [sigma_1, sigma_2, sigma_3];
        let z_polys = [z_poly_0, z_poly_1, z_poly_2];

        let permutation_eval = permutation_argument
            .open_argument(
                l_0_eval,
                l_u_eval,
                &q_blind,
                &z_polys,
                &permutation_oracles,
                &witness_oracles,
                beta,
                gamma,
                &domain,
                evaluation_challenge,
                &powers_of_alpha,
            )
            .unwrap();

        assert_eq!(permutation_eval, q_eval * zh_eval);
    }

    #[test]
    fn copy_plonk() {
        /*
            We encode circuit x^3 + 2x + 12 = 0, (solution x = -2, -2 ^3 + 2*(-2) + 12 = -8 - 4 + 12 = 0)

            gate0: a0 * b0 = c0 |==> x * x = x^2
            gate1: a1 * b1 = c1 |==> x^2 * x = x^3
            gate2: b2 = PI[2]   |==> b2 = 2
            gate3: a3 * b3 = c3 |==> 2x = 2 * x
            gate4: a4 + b4 = c4 |==> x^3 + 2x
            gate5: b5 = PI[5]   |==> b5 = 12
            gate6: a5 + b5 = c5 |==> x3 + 2x + 12
            gate7: c5 = PI[5]   |==> c5 == 0


            * -> can be whatever

            row        a       b      c         PI

            0          x       x      x^2       0     copy: a0 = b0

            1          x^2     x      x^3       0     copy: a1 = c0, b1 = a0

            2          *       2       *        2     copy:

            3          x       2       2x       0     copy: a3 = a0, b2 = b3

            4          x^3     2x     x^3+2x    0     copy: a4 = c1, b4 = c3

            5           *      12       *       12     copy:

            6         x^3+2x   12     x^3+2x+12  0     copy: a6 = c4, b5 = b6

            7           *       *     x^3+2x+12  0     copy  c6 = c7


            a_evals = [x, x^2, dummy, x, x^3, dummy, x^3 + 2x, dummy, blinds...]

            b_evals = [x, x, 2, 2, 2x, 12, 12, dummy, blinds...]

            c_evals = [x^2, x^3, dummy, 2x, x^3 + 2x, dummy, x^3+2x+12, x^3+2x+12, blinds...]


            cycles:
                (a0, b0, b1, a3) (a1, c0) (b2, b3) (a4, c1) (b4, c3) (a6, c4) (b5, b6) (c6, c7)


            Begin NOTE:
            When we use permutation we need one more element to encode full accumulation in z(X)
            consider simple example without rotations:
            a =  [a0, a1, a2]
            b =  [b0, b1, b2]

            a, b both can fit in domain of k = 4, 3 evals + 1 blinding

            But:
            z =  [1, a0/b0, a0a1/b0b1, a0a1a2/b0b1b2] + 2 random elements for blinding because z(X) is being opened in x and wx
            END Note:

            Our polynomials can fit in k = 8, 7 evals + 1 blinding but because of the above mentioned problem we have to work in domain of k = 16

            Usable rows are: u = 8 (because z(X) needs one more eval)
            we an use rest of rows to blind

            q_last =  [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
            q_blind = [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1]
        */

        let mut rng = test_rng();
        let domain_size = 16;
        let max_degree = domain_size - 1;

        let srs = PilInstance::universal_setup(max_degree, &mut rng).unwrap();

        let (ck, verifier_key) = PilInstance::prepare_keys(&srs).unwrap();

        let fill_zeroes = |evals: &mut Vec<F>| {
            let zeroes = vec![F::zero(); domain_size - evals.len()];
            evals.extend_from_slice(&zeroes);
        };

        let fill_blinds = |evals: &mut Vec<F>| {
            let mut rng = test_rng();
            let blinds = vec![F::rand(&mut rng); domain_size - evals.len()];
            evals.extend_from_slice(&blinds);
        };

        let domain_size = 16;
        let poly_degree = domain_size - 1;
        let _max_degree = poly_degree;

        let domain = GeneralEvaluationDomain::<F>::new(domain_size).unwrap();

        let x = -F::from(2u64);
        let x_squared = x * x;
        let x_cube = x * x_squared;

        let two = F::from(2u64);
        let two_x = two * x;

        let twelve = F::from(12u64);

        let zero = F::zero();
        let one = F::one();

        let dummy = F::from(999u64);

        let fill_dummy = |evals: &mut Vec<F>| {
            let dummys = vec![dummy.clone(); domain_size - evals.len()];
            evals.extend_from_slice(&dummys);
        };

        let mut a_evals =
            vec![x, x_squared, dummy, x, x_cube, dummy, x_cube + two_x, dummy];

        let mut b_evals = vec![x, x, two, two, two_x, twelve, twelve, dummy];

        let mut c_evals = vec![
            x_squared,
            x_cube,
            dummy,
            two_x,
            x_cube + two_x,
            dummy,
            x_cube + two_x + twelve,
            x_cube + two_x + twelve,
        ];

        let mut pi_evals =
            vec![zero, zero, two, zero, zero, twelve, zero, zero];

        let mut qm_evals = vec![one, one, zero, one, zero, zero, zero, zero];

        let mut ql_evals = vec![zero, zero, zero, zero, one, zero, one, zero];

        let mut qr_evals = vec![zero, zero, -one, zero, one, -one, one, zero];

        let mut qo_evals = vec![-one, -one, zero, -one, -one, zero, -one, -one];
        let qc_evals = vec![F::zero(); domain_size];

        assert_eq!(x_cube + two_x + twelve, zero);

        fill_zeroes(&mut pi_evals);
        fill_zeroes(&mut qm_evals);
        fill_zeroes(&mut ql_evals);
        fill_zeroes(&mut qr_evals);
        fill_zeroes(&mut qo_evals);

        fill_blinds(&mut a_evals);
        fill_blinds(&mut b_evals);
        fill_blinds(&mut c_evals);

        // Here we check that circuit is satisfiable
        for i in 0..domain.size() {
            let arith = qm_evals[i] * a_evals[i] * b_evals[i]
                + ql_evals[i] * a_evals[i]
                + qr_evals[i] * b_evals[i]
                + qo_evals[i] * c_evals[i]
                + pi_evals[i];

            assert_eq!(arith, F::zero());
        }

        let deltas = [one, F::from(7u64), F::from(13u64)];

        // cycles:
        // (a0, b0, b1, a3) (b2, b3) (b5, b6) (c6, c7) (a1, c0) (a4, c1) (a6, c4) (b4, c3)

        // skip for now

        /*
            a0 -> b0
            a1 -> c0
            a2 -> a2
            a3 -> a0
            a4 -> c1
            a5 -> a5
            a6 -> c4
            a7 -> a7
            ...fill dummys
        */

        let mut sigma_1_evals = vec![
            deltas[1] * domain.element(0), //0
            deltas[2] * domain.element(0), //1
            deltas[0] * domain.element(2), //2
            deltas[0] * domain.element(0), //3
            deltas[2] * domain.element(1), //4
            deltas[0] * domain.element(5), //5
            deltas[2] * domain.element(4), //6
            deltas[0] * domain.element(7), //7
        ];

        fill_dummy(&mut sigma_1_evals);

        // cycles:
        // (a0, b0, b1, a3) (b2, b3) (b5, b6) (c6, c7) (a1, c0) (a4, c1) (a6, c4) (b4, c3)

        // skip for now

        /*
            b0 -> b1
            b1 -> a3
            b2 -> b3
            b3 -> b2
            b4 -> c3
            b5 -> b6
            b6 -> b5
            b7 -> b7
            ...fill dummys
        */

        let mut sigma_2_evals = vec![
            deltas[1] * domain.element(1), //0
            deltas[0] * domain.element(3), //1
            deltas[1] * domain.element(3), //2
            deltas[1] * domain.element(2), //3
            deltas[2] * domain.element(3), //4
            deltas[1] * domain.element(6), //5
            deltas[1] * domain.element(5), //6
            deltas[1] * domain.element(7), //7
        ];

        fill_dummy(&mut sigma_2_evals);

        // cycles:
        // (a0, b0, b1, a3) (b2, b3) (b5, b6) (c6, c7) (a1, c0) (a4, c1) (a6, c4) (b4, c3)

        // skip for now
        /*
            c0 -> a1
            c1 -> a4
            c2 -> c2
            c3 -> b4
            c4 -> a6
            c5 -> c5
            c6 -> c7
            c7 -> c6
            ...fill dummys
        */

        let mut sigma_3_evals = vec![
            deltas[0] * domain.element(1), //0
            deltas[0] * domain.element(4), //1
            deltas[2] * domain.element(2), //2
            deltas[1] * domain.element(4), //3
            deltas[0] * domain.element(6), //4
            deltas[2] * domain.element(5), //5
            deltas[2] * domain.element(7), //6
            deltas[2] * domain.element(6), //7
        ];

        fill_dummy(&mut sigma_3_evals);

        // assert_eq!(c_evals[6] * sigma_3_evals[6], c_evals[7]  * sigma_3_evals[7]);

        // println!("Surv")

        let u = 8; // see Note at comment on top
        let beta = F::rand(&mut rng);
        let gamma = F::rand(&mut rng);

        let mut z_evals = vec![];
        let mut z_prev = F::one();
        z_evals.push(z_prev);

        let omegas: Vec<F> = domain.elements().collect();

        for i in 0..u {
            let nom_a = a_evals[i] + beta * deltas[0] * omegas[i] + gamma;
            let nom_b = b_evals[i] + beta * deltas[1] * omegas[i] + gamma;
            let nom_c = c_evals[i] + beta * deltas[2] * omegas[i] + gamma;

            let denom_a = a_evals[i] + beta * sigma_1_evals[i] + gamma;
            let denom_b = b_evals[i] + beta * sigma_2_evals[i] + gamma;
            let denom_c = c_evals[i] + beta * sigma_3_evals[i] + gamma;

            let nom = nom_a * nom_b * nom_c;
            let denom = denom_a * denom_b * denom_c;

            z_prev *= nom * denom.inverse().unwrap();
            z_evals.push(z_prev);
        }

        assert_eq!(z_evals[u], F::one());

        fill_dummy(&mut z_evals);

        let a_poly =
            DensePolynomial::from_coefficients_slice(&domain.ifft(&a_evals));
        let b_poly =
            DensePolynomial::from_coefficients_slice(&domain.ifft(&b_evals));
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
        let qc_poly =
            DensePolynomial::from_coefficients_slice(&domain.ifft(&qc_evals));

        let sigma_1_poly = DensePolynomial::from_coefficients_slice(
            &domain.ifft(&sigma_1_evals),
        );
        let sigma_2_poly = DensePolynomial::from_coefficients_slice(
            &domain.ifft(&sigma_2_evals),
        );
        let sigma_3_poly = DensePolynomial::from_coefficients_slice(
            &domain.ifft(&sigma_3_evals),
        );

        // Witness oracles
        let mut a = WitnessProverOracle {
            label: "a".to_string(),
            poly: a_poly.clone(),
            evals_at_coset_of_extended_domain: None,
            queried_rotations: BTreeSet::default(),
            should_permute: true,
            evals: a_evals,
        };

        let mut b = WitnessProverOracle {
            label: "b".to_string(),
            poly: b_poly.clone(),
            evals_at_coset_of_extended_domain: None,
            queried_rotations: BTreeSet::default(),
            should_permute: true,
            evals: b_evals,
        };

        let mut c = WitnessProverOracle {
            label: "c".to_string(),
            poly: c_poly.clone(),
            evals_at_coset_of_extended_domain: None,
            queried_rotations: BTreeSet::default(),
            should_permute: true,
            evals: c_evals,
        };

        // Instance oracles
        let mut pi = InstanceProverOracle {
            label: "pi".to_string(),
            poly: pi_poly.clone(),
            evals: pi_evals.clone(),
            evals_at_coset_of_extended_domain: None,
            queried_rotations: BTreeSet::default(),
        };

        // Fixed oracles
        let mut qm = FixedProverOracle::<F>::new("qm", qm_poly.clone(), &qm_evals);
        let mut ql = FixedProverOracle::<F>::new("ql", ql_poly.clone(), &ql_evals);
        let mut qr = FixedProverOracle::<F>::new("qr", qr_poly.clone(), &qr_evals);
        let mut qo = FixedProverOracle::<F>::new("qo", qo_poly.clone(), &qo_evals);
        let mut qc = FixedProverOracle::<F>::new("qc", qc_poly.clone(), &qc_evals);

        // Permutation polynomials
        let sigma1 = FixedProverOracle {
            label: "sigma_1".to_string(),
            poly: sigma_1_poly.clone(),
            evals_at_coset_of_extended_domain: None,
            evals: sigma_1_evals,
            queried_rotations: BTreeSet::from([Rotation::curr()]),
        };

        let sigma2 = FixedProverOracle {
            label: "sigma_2".to_string(),
            poly: sigma_2_poly.clone(),
            evals_at_coset_of_extended_domain: None,
            evals: sigma_2_evals,
            queried_rotations: BTreeSet::from([Rotation::curr()]),
        };

        let sigma3 = FixedProverOracle {
            label: "sigma_3".to_string(),
            poly: sigma_3_poly.clone(),
            evals_at_coset_of_extended_domain: None,
            evals: sigma_3_evals,
            queried_rotations: BTreeSet::from([Rotation::curr()]),
        };

        let mut q_blind_evals = vec![F::one(); domain.size()];
        for i in 0..=u {
            q_blind_evals[i] = F::zero();
        }

        let q_blind_poly = DensePolynomial::<F>::from_coefficients_slice(
            &domain.ifft(&q_blind_evals),
        );

        let q_blind = FixedProverOracle {
            label: "q_blind".to_string(),
            poly: q_blind_poly.clone(),
            evals_at_coset_of_extended_domain: None,
            evals: q_blind_evals.to_vec(),
            queried_rotations: BTreeSet::from([Rotation::curr()]),
        };

        let mut witness_oracles: &mut [&mut WitnessProverOracle<F>] = &mut [&mut a, &mut b, &mut c];
        let mut instance_oracles: &mut [&mut InstanceProverOracle<F>] = &mut [&mut pi];
        let mut fixed_oracles: &mut [&mut FixedProverOracle<F>] = &mut [
            &mut qm,
            &mut ql,
            &mut qr,
            &mut qo,
            &mut qc,
        ];

        let permutation_oracles = [sigma1, sigma2, sigma3];

        let mut plonk_vo =
            GenericVO::<F>::init(PrecompiledPlonkArith::get_expr_and_queries());

        plonk_vo.configure(
            &mut witness_oracles,
            &mut instance_oracles,
            &mut fixed_oracles,
        );

        let vos: Vec<&dyn VirtualOracle<F>> = vec![&plonk_vo];

        let permutation_info = PermutationInfo {
            u,
            deltas: deltas.to_vec(),
        };

        let vk = Indexer::<F, PC>::index(
            &verifier_key,
            &vos,
            vec![],
            &witness_oracles,
            &instance_oracles,
            &fixed_oracles,
            domain,
            &domain.vanishing_polynomial().into(),
            permutation_info.clone(),
            u,
        )
        .unwrap();
        
        let pk = ProverKey::from_ck_and_vk(&ck, &vk);

        let mut preprocessed = ProverPreprocessedInput::new(
            fixed_oracles,
            &permutation_oracles.to_vec(),
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

        let mut a_ver = WitnessVerifierOracle::<F, PC> {
            label: "a".to_string(),
            queried_rotations: BTreeSet::new(),
            should_permute: true,
            evals_at_challenges: BTreeMap::default(),
            commitment: None,
        };
        let mut b_ver = WitnessVerifierOracle::<F, PC> {
            label: "b".to_string(),
            queried_rotations: BTreeSet::new(),
            should_permute: true,
            evals_at_challenges: BTreeMap::default(),
            commitment: None,
        };
        let mut c_ver = WitnessVerifierOracle::<F, PC> {
            label: "c".to_string(),
            queried_rotations: BTreeSet::new(),
            should_permute: true,
            evals_at_challenges: BTreeMap::default(),
            commitment: None,
        };


        let mut witness_ver_oracles: &mut [&mut WitnessVerifierOracle<F, PC>] = &mut [
            &mut a_ver,
            &mut b_ver,
            &mut c_ver,
        ];

        let mut pi = InstanceVerifierOracle {
            label: "pi".to_string(),
            poly: pi_poly.clone(),
            evals: pi_evals.clone(),
            queried_rotations: BTreeSet::new(),
        };

        let mut instance_oracles: &mut [&mut InstanceVerifierOracle<F>] = &mut [&mut pi];

        let labeled_selectors: Vec<LabeledPolynomial<F, DensePolynomial<F>>> =
            [
                (qm_poly.clone(), "qm"),
                (ql_poly.clone(), "ql"),
                (qr_poly.clone(), "qr"),
                (qo_poly.clone(), "qo"),
                (DensePolynomial::zero(), "qc"),
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

        let mut selector_oracles_raw: Vec<_> = selector_commitments
            .iter()
            .map(|cmt| FixedVerifierOracle::<F, PC> {
                label: cmt.label().clone(),
                queried_rotations: BTreeSet::default(),
                evals_at_challenges: BTreeMap::default(),
                commitment: Some(cmt.commitment().clone()),
            })
            .collect();

        let mut selector_oracles_v: Vec<&mut FixedVerifierOracle<F, PC>> = selector_oracles_raw
            .iter_mut()
            .collect();
        let mut selector_oracles: &mut [&mut FixedVerifierOracle<F, PC>] = selector_oracles_v.iter_mut().into_slice();

        let labeled_sigmas: Vec<LabeledPolynomial<F, DensePolynomial<F>>> = [
            (sigma_1_poly.clone(), "sigma_1"),
            (sigma_2_poly.clone(), "sigma_2"),
            (sigma_3_poly.clone(), "sigma_3"),
        ]
        .iter()
        .map(|(poly, label)| {
            LabeledPolynomial::new(label.to_string(), poly.clone(), None, None)
        })
        .collect();

        let (sigma_commitments, _) =
            PC::commit(&ck, labeled_sigmas.iter(), None).unwrap();

        let sigma_oracles: Vec<_> = sigma_commitments
            .iter()
            .map(|cmt| FixedVerifierOracle::<F, PC> {
                label: cmt.label().clone(),
                queried_rotations: BTreeSet::from([Rotation::curr()]),
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

        let mut plonk_vo =
            GenericVO::<F>::init(PrecompiledPlonkArith::get_expr_and_queries());

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
            vec![],
            &witness_ver_oracles,
            &instance_oracles,
            &selector_oracles,
            domain,
            &domain.vanishing_polynomial().into(),
            permutation_info,
            u,
        )
        .unwrap();

        let mut verifier_pp = VerifierPreprocessedInput {
            fixed_oracles: selector_oracles,
            table_oracles: vec![],
            permutation_oracles: sigma_oracles.clone(),
            q_blind,
        };

        // We clone because fixed oracles must be mutable in order to add evals at challenge
        // Another option is to create reset method which will just reset challenge to eval mapping
        // This is anyway just mockup of frontend
        //let mut pp_clone = verifier_pp.clone();

        let res = PilInstance::verify(
            &mut vk,
            &mut verifier_pp,
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
