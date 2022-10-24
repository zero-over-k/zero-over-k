use std::{collections::BTreeSet, marker::PhantomData};

use ark_ff::PrimeField;
use ark_poly::{
    univariate::DensePolynomial, EvaluationDomain, GeneralEvaluationDomain,
    UVPolynomial,
};
use ark_std::rand::Rng;

use crate::{
    commitment::HomomorphicCommitment,
    oracles::{
        fixed::{FixedProverOracle, FixedVerifierOracle},
        rotation::Rotation,
        traits::{ConcreteOracle, Instantiable},
        witness::{WitnessProverOracle, WitnessVerifierOracle},
    },
};

pub struct SubsetEqualityArgument<F: PrimeField> {
    _f: PhantomData<F>,
}

impl<F: PrimeField> SubsetEqualityArgument<F> {
    pub fn construct_agg_poly<R: Rng>(
        a: &WitnessProverOracle<F>,
        s: &WitnessProverOracle<F>,
        a_prime: &WitnessProverOracle<F>,
        s_prime: &WitnessProverOracle<F>,
        beta: F,
        gamma: F,
        lookup_index: usize,
        u: usize, // allowed rows
        domain: &GeneralEvaluationDomain<F>,
        extended_coset_domain: &GeneralEvaluationDomain<F>,
        zk_rng: &mut R,
    ) -> WitnessProverOracle<F> {
        let mut z_evals = Vec::with_capacity(domain.size());
        let mut z_prev = F::one();
        z_evals.push(z_prev);

        for i in 0..u {
            let num = (a.evals[i] + beta) * (s.evals[i] + gamma);
            let denom = (a_prime.evals[i] + beta) * (s_prime.evals[i] + gamma);

            z_prev *= num * denom.inverse().unwrap();
            z_evals.push(z_prev);
        }

        // allowed rows is: u = domain_size - t - 1
        // t = domain_size - 1 - u
        // so blind with t evals
        let t = domain.size() - 1 - u;
        for _ in 0..t {
            z_evals.push(F::rand(zk_rng));
        }

        let poly =
            DensePolynomial::from_coefficients_slice(&domain.ifft(&z_evals));

        WitnessProverOracle {
            label: format!("lookup_{}_agg_poly", lookup_index).to_string(),
            evals_at_coset_of_extended_domain: Some(
                extended_coset_domain.coset_fft(&poly),
            ),
            poly: poly,
            evals: z_evals,
            queried_rotations: BTreeSet::from([
                Rotation::curr(),
                Rotation::next(),
            ]),
            should_permute: false,
        }
    }

    /// this function cares about:
    /// 1. Z(w^0) = 1
    /// 2. Subset equality check
    /// 3. Z(w^u) = 0 or 1
    pub fn instantiate_argument_at_omega_i(
        l0_coset_evals: &Vec<F>,
        q_last_coset_evals: &Vec<F>,
        q_blind: &FixedProverOracle<F>,
        a: &WitnessProverOracle<F>,
        s: &WitnessProverOracle<F>,
        a_prime: &WitnessProverOracle<F>,
        s_prime: &WitnessProverOracle<F>,
        z: &WitnessProverOracle<F>,
        beta: F,
        gamma: F,
        omega_index: usize,
        alpha_powers: &Vec<F>,
    ) -> F {
        assert_eq!(alpha_powers.len(), 3);

        let mut num = F::zero();

        let a_x = a.query_in_coset(omega_index, Rotation::curr());
        let a_prime_x = a_prime.query_in_coset(omega_index, Rotation::curr());

        let s_x = s.query_in_coset(omega_index, Rotation::curr());
        let s_prime_x = s_prime.query_in_coset(omega_index, Rotation::curr());

        let z_x = z.query_in_coset(omega_index, Rotation::curr());
        let z_wx = z.query_in_coset(omega_index, Rotation::next());

        let q_blind_x = q_blind.query_in_coset(omega_index, Rotation::curr());

        num += alpha_powers[0] * l0_coset_evals[omega_index] * (F::one() - z_x);

        let equality_part = {
            let zk_part =
                F::one() - (q_blind_x + q_last_coset_evals[omega_index]);

            let lhs = z_wx * (a_prime_x + beta) * (s_prime_x + gamma);
            let rhs = z_x * (a_x + beta) * (s_x + gamma);

            zk_part * (lhs - rhs)
        };

        num += alpha_powers[1] * equality_part;

        num += alpha_powers[2]
            * q_last_coset_evals[omega_index]
            * (z_x * z_x - z_x);

        num
    }

    pub fn open_argument<PC: HomomorphicCommitment<F>>(
        l0_eval: &F,
        q_last_eval: F,
        q_blind: &FixedVerifierOracle<F, PC>,
        a: &WitnessVerifierOracle<F, PC>,
        s: &WitnessVerifierOracle<F, PC>,
        a_prime: &WitnessVerifierOracle<F, PC>,
        s_prime: &WitnessVerifierOracle<F, PC>,
        z: &WitnessVerifierOracle<F, PC>,
        beta: F,
        gamma: F,
        evaluation_challenge: &F,
        domain: &GeneralEvaluationDomain<F>,
        alpha_powers: &Vec<F>,
    ) -> F {
        assert_eq!(alpha_powers.len(), 3);
        let shifted_evaluation_challenge =
            domain.element(1) * evaluation_challenge;

        let mut opening = F::zero();

        let a_xi = a.query(&evaluation_challenge);
        let a_prime_xi = a_prime.query(&evaluation_challenge);

        let s_xi = s.query(&evaluation_challenge);
        let s_prime_xi = s_prime.query(&evaluation_challenge);

        let z_xi = z.query(&evaluation_challenge);
        let z_wxi = z.query(&shifted_evaluation_challenge);

        opening += alpha_powers[0] * l0_eval * (F::one() - z_xi);

        let zk_part =
            F::one() - (q_last_eval + q_blind.query(evaluation_challenge));
        let lhs = z_wxi * (a_prime_xi + beta) * (s_prime_xi + gamma);
        let rhs = z_xi * (a_xi + beta) * (s_xi + gamma);

        opening += alpha_powers[1] * zk_part * (lhs - rhs);

        opening += alpha_powers[2] * q_last_eval * (z_xi * z_xi - z_xi);

        opening
    }
}

#[cfg(test)]
mod test {
    use std::collections::{BTreeMap, BTreeSet};

    use ark_bls12_381::{Bls12_381, Fr as F};
    use ark_ff::{batch_inversion, One, UniformRand, Zero};
    use ark_poly::univariate::DensePolynomial;
    use ark_poly::{
        EvaluationDomain, GeneralEvaluationDomain, Polynomial, UVPolynomial,
    };
    use ark_std::test_rng;

    use shuffle::irs::Irs;
    use shuffle::shuffler::Shuffler;

    use crate::oracles::fixed::{FixedProverOracle, FixedVerifierOracle};
    use crate::oracles::rotation::Rotation;
    use crate::oracles::witness::{WitnessProverOracle, WitnessVerifierOracle};
    use crate::util::compute_vanishing_poly_over_coset;

    use super::SubsetEqualityArgument;

    use crate::commitment::KZG10;
    type PC = KZG10<Bls12_381>;

    #[test]
    fn test_subset_equality_argument() {
        let domain_size = 16;
        let poly_degree = domain_size - 1;
        let mut rng = test_rng();

        let domain = GeneralEvaluationDomain::new(domain_size).unwrap();

        let scaling_factor = 4;
        let extended_coset_domain =
            GeneralEvaluationDomain::<F>::new(scaling_factor * domain_size)
                .unwrap();

        let u = 10;

        let mut a_evals: Vec<F> = (0..u).map(|_| F::rand(&mut rng)).collect();
        let mut s_evals: Vec<F> = (0..u).map(|_| F::rand(&mut rng)).collect();

        let mut a_prime_evals = a_evals[..].to_vec();
        let mut s_prime_evals = s_evals[..].to_vec();

        let mut irs = Irs::default();

        irs.shuffle(&mut a_prime_evals, &mut rng).unwrap();
        irs.shuffle(&mut s_prime_evals, &mut rng).unwrap();

        // blind
        for _ in u..domain_size {
            a_evals.push(F::rand(&mut rng));
            a_prime_evals.push(F::rand(&mut rng));
            s_evals.push(F::rand(&mut rng));
            s_prime_evals.push(F::rand(&mut rng));
        }

        assert_eq!(a_evals.len(), domain_size);

        let a_poly =
            DensePolynomial::from_coefficients_slice(&domain.ifft(&a_evals));
        let a = WitnessProverOracle {
            label: "a".to_string(),
            poly: a_poly.clone(),
            evals: a_evals.clone(),
            evals_at_coset_of_extended_domain: Some(
                extended_coset_domain.coset_fft(&a_poly),
            ),
            queried_rotations: BTreeSet::from([Rotation::curr()]),
            should_permute: false,
        };

        let a_prime_poly = DensePolynomial::from_coefficients_slice(
            &domain.ifft(&a_prime_evals),
        );
        let a_prime = WitnessProverOracle {
            label: "a_prime".to_string(),
            poly: a_prime_poly.clone(),
            evals: a_prime_evals.clone(),
            evals_at_coset_of_extended_domain: Some(
                extended_coset_domain.coset_fft(&a_prime_poly),
            ),
            queried_rotations: BTreeSet::from([Rotation::curr()]),
            should_permute: false,
        };

        let s_poly =
            DensePolynomial::from_coefficients_slice(&domain.ifft(&s_evals));
        let s = WitnessProverOracle {
            label: "s".to_string(),
            poly: s_poly.clone(),
            evals: s_evals.clone(),
            evals_at_coset_of_extended_domain: Some(
                extended_coset_domain.coset_fft(&s_poly),
            ),
            queried_rotations: BTreeSet::from([Rotation::curr()]),
            should_permute: false,
        };

        let s_prime_poly = DensePolynomial::from_coefficients_slice(
            &domain.ifft(&s_prime_evals),
        );
        let s_prime = WitnessProverOracle {
            label: "s_prime".to_string(),
            poly: s_prime_poly.clone(),
            evals: s_prime_evals.clone(),
            evals_at_coset_of_extended_domain: Some(
                extended_coset_domain.coset_fft(&s_prime_poly),
            ),
            queried_rotations: BTreeSet::from([Rotation::curr()]),
            should_permute: false,
        };

        let beta = F::rand(&mut rng);
        let gamma = F::rand(&mut rng);

        let z = SubsetEqualityArgument::construct_agg_poly(
            &a,
            &s,
            &a_prime,
            &s_prime,
            beta,
            gamma,
            0,
            u,
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

        let t = domain_size - 1 - u;
        let mut q_blind_evals = vec![F::zero(); u + 1];
        let to_extend = vec![F::one(); t];
        q_blind_evals.extend_from_slice(&to_extend);

        assert_eq!(q_blind_evals.len(), domain_size);

        let q_blind_poly = DensePolynomial::from_coefficients_slice(
            &domain.ifft(&q_blind_evals),
        );
        let q_blind = FixedProverOracle {
            label: "q_blind".to_string(),
            poly: q_blind_poly.clone(),
            evals: q_blind_evals.clone(),
            evals_at_coset_of_extended_domain: Some(
                extended_coset_domain.coset_fft(&q_blind_poly),
            ),
            queried_rotations: BTreeSet::from([Rotation::curr()]),
        };

        let alpha = F::rand(&mut rng);
        let alpha_powers = vec![F::one(), alpha, alpha * alpha];

        let mut num_evals =
            Vec::<F>::with_capacity(extended_coset_domain.size());
        for i in 0..extended_coset_domain.size() {
            let ni = SubsetEqualityArgument::instantiate_argument_at_omega_i(
                &l0_coset_evals,
                &lu_coset_evals,
                &q_blind,
                &a,
                &s,
                &a_prime,
                &s_prime,
                &z,
                beta,
                gamma,
                i,
                &alpha_powers,
            );

            num_evals.push(ni);
        }

        let mut zh_inverse_evals = compute_vanishing_poly_over_coset(
            extended_coset_domain,
            domain_size as u64,
        );
        batch_inversion(&mut zh_inverse_evals);

        let q_evals: Vec<F> = num_evals
            .iter()
            .zip(zh_inverse_evals.iter())
            .map(|(&num, denom)| num * denom)
            .collect();
        let q = DensePolynomial::from_coefficients_slice(
            &extended_coset_domain.coset_ifft(&q_evals),
        );

        let evaluation_challenge = F::rand(&mut rng);

        let a = WitnessVerifierOracle {
            label: "a".to_string(),
            queried_rotations: BTreeSet::from([Rotation::curr()]),
            evals_at_challenges: BTreeMap::from([(
                evaluation_challenge,
                a_poly.evaluate(&evaluation_challenge),
            )]),
            commitment: None,
            should_permute: false,
        };

        let a_prime = WitnessVerifierOracle {
            label: "a_prime".to_string(),
            queried_rotations: BTreeSet::from([Rotation::curr()]),
            evals_at_challenges: BTreeMap::from([(
                evaluation_challenge,
                a_prime_poly.evaluate(&evaluation_challenge),
            )]),
            commitment: None,
            should_permute: false,
        };

        let s = WitnessVerifierOracle {
            label: "s".to_string(),
            queried_rotations: BTreeSet::from([Rotation::curr()]),
            evals_at_challenges: BTreeMap::from([(
                evaluation_challenge,
                s_poly.evaluate(&evaluation_challenge),
            )]),
            commitment: None,
            should_permute: false,
        };

        let s_prime = WitnessVerifierOracle {
            label: "s_prime".to_string(),
            queried_rotations: BTreeSet::from([Rotation::curr()]),
            evals_at_challenges: BTreeMap::from([(
                evaluation_challenge,
                s_prime_poly.evaluate(&evaluation_challenge),
            )]),
            commitment: None,
            should_permute: false,
        };

        let q_blind = FixedVerifierOracle {
            label: "q_blind".to_string(),
            queried_rotations: BTreeSet::from([Rotation::curr()]),
            evals_at_challenges: BTreeMap::from([(
                evaluation_challenge,
                q_blind_poly.evaluate(&evaluation_challenge),
            )]),
            commitment: None,
        };

        let z = WitnessVerifierOracle {
            label: "lookup_agg_poly".to_string(),
            queried_rotations: BTreeSet::from([
                Rotation::curr(),
                Rotation::next(),
            ]),
            evals_at_challenges: BTreeMap::from([
                (evaluation_challenge, z.poly.evaluate(&evaluation_challenge)),
                (
                    evaluation_challenge * domain.element(1),
                    z.poly
                        .evaluate(&(evaluation_challenge * domain.element(1))),
                ),
            ]),
            commitment: None,
            should_permute: false,
        };

        let l0_eval = l0.evaluate(&evaluation_challenge);
        let lu_eval = lu.evaluate(&evaluation_challenge);

        let opening = SubsetEqualityArgument::open_argument::<PC>(
            &l0_eval,
            lu_eval,
            &q_blind,
            &a,
            &s,
            &a_prime,
            &s_prime,
            &z,
            beta,
            gamma,
            &evaluation_challenge,
            &domain,
            &alpha_powers,
        );

        assert_eq!(
            opening,
            q.evaluate(&evaluation_challenge)
                * domain
                    .vanishing_polynomial()
                    .evaluate(&evaluation_challenge)
        )
    }
}
