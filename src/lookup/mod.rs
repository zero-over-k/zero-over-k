use std::{
    collections::{BTreeMap, BTreeSet},
    iter::successors,
    marker::PhantomData,
};

use ark_ff::PrimeField;
use ark_poly::{
    univariate::DensePolynomial, EvaluationDomain, GeneralEvaluationDomain,
    UVPolynomial,
};
use ark_std::rand::Rng;

use crate::{
    commitment::HomomorphicCommitment,
    lookup::{
        permute::permute_for_lookup, subset_equality::SubsetEqualityArgument,
    },
    oracles::{
        fixed::{FixedProverOracle, FixedVerifierOracle},
        instance::{InstanceProverOracle, InstanceVerifierOracle},
        query::{OracleQuery, OracleType},
        rotation::Rotation,
        traits::{CommittedOracle, ConcreteOracle, Instantiable},
        witness::{WitnessProverOracle, WitnessVerifierOracle},
    },
    vo::new_expression::NewExpression,
};

pub mod permute;
pub mod subset_equality;

pub struct LookupArgument<F: PrimeField> {
    _f: PhantomData<F>,
}

impl<F: PrimeField> LookupArgument<F> {
    /*
       In subset equality argument we have q_blind * z(wX) * A'(X) * S'(X) = 4n - 4
       Then - n for vanishing gives 3n - 4, but still we have to work in 4n
    */
    pub const MINIMAL_SCALING_FACTOR: usize = 4;

    pub fn construct_a_and_s_polys_prover<'a, R: Rng>(
        witness_oracles_mapping: &BTreeMap<String, usize>,
        instance_oracles_mapping: &BTreeMap<String, usize>,
        fixed_oracles_mapping: &BTreeMap<String, usize>,
        table_oracles_mapping: &BTreeMap<String, usize>,
        witness_oracles: &'a [WitnessProverOracle<F>],
        instance_oracles: &'a [InstanceProverOracle<F>],
        fixed_oracles: &'a [FixedProverOracle<F>],
        table_oracles: &'a [FixedProverOracle<F>],
        usable_rows: usize,
        lookup_index: usize,
        lookup_expressions: &[NewExpression<F>],
        table_queries: &[OracleQuery],
        theta: F, // lookup aggregation expression
        domain: &GeneralEvaluationDomain<F>,
        extended_coset_domain: &GeneralEvaluationDomain<F>,
        zk_rng: &mut R,
    ) -> (
        WitnessProverOracle<F>,
        WitnessProverOracle<F>,
        WitnessProverOracle<F>,
        WitnessProverOracle<F>,
    ) {
        // When working on prover we want to construct A, A', S and S' as WitnessProverOracles
        // We need both polys and coset evals for them, one approach is to compute polynomials and then to do coset fft
        // But it's faster if we evaluate expression 2 times, one in coset and one in just domain
        // 1. compute all expressions and and all table queries in original domain and coset
        // 2. compress them to derive A and S
        // 3. Permute a_evals and s_evals to get a_prime_evals and s_prime_evals
        // 4. Compute cosets and polys for a_prime and s_prime

        // each lookup expressions is matched with one table query
        assert_eq!(lookup_expressions.len(), table_queries.len());
        let lookup_arith = lookup_expressions.len();

        let powers_of_theta: Vec<F> =
            successors(Some(F::one()), |theta_i| Some(*theta_i * theta))
                .take(lookup_arith)
                .collect();

        let mut a_original_domain_evals =
            Vec::<F>::with_capacity(domain.size());
        let mut a_extended_coset_domain_evals =
            Vec::<F>::with_capacity(domain.size());

        for i in 0..domain.size() {
            let expressions_at_i = lookup_expressions.iter().map(|lookup_expr| {
                lookup_expr.evaluate(
                    &|x: F| x,
                    &|query| {
                        // let point = 
                        match query.oracle_type {
                            OracleType::Witness => {
                                match witness_oracles_mapping.get(&query.label) {
                                    Some(index) => witness_oracles[*index].query_at_omega_in_original_domain(i, query.rotation),
                                    None => panic!("Witness oracle with label add_label not found")
                                }
                            },
                            OracleType::Instance => {
                                match instance_oracles_mapping.get(&query.label) {
                                    Some(index) => instance_oracles[*index].query_at_omega_in_original_domain(i, query.rotation),
                                    None => panic!("Instance oracle with label add_label not found")
                                }
                            },
                            OracleType::Fixed => {
                                match fixed_oracles_mapping.get(&query.label) {
                                    Some(index) => fixed_oracles[*index].query_at_omega_in_original_domain(i, query.rotation),
                                    None => panic!("Fixed oracle with label add_label not found")
                                }
                            },
                        }
                    },
                    &|x: F| -x,
                    &|x: F, y: F| x + y,
                    &|x: F, y: F| x * y,
                    &|x: F, y: F| x * y,
                )
            });

            let mut agg = F::zero();
            for (expr_i, theta_i) in
                expressions_at_i.zip(powers_of_theta.iter())
            {
                agg += expr_i * theta_i
            }

            a_original_domain_evals.push(agg);
        }

        for i in 0..extended_coset_domain.size() {
            let expressions_at_i = lookup_expressions.iter().map(|lookup_expr| {
                lookup_expr.evaluate(
                    &|x: F| x,
                    &|query| {
                        match query.oracle_type {
                            OracleType::Witness => {
                                match witness_oracles_mapping.get(&query.label) {
                                    Some(index) => witness_oracles[*index].query_in_coset(i, query.rotation),
                                    None => panic!("Witness oracle with label {} not found", query.label)
                                }
                            },
                            OracleType::Instance => {
                                match instance_oracles_mapping.get(&query.label) {
                                    Some(index) => instance_oracles[*index].query_in_coset(i, query.rotation),
                                    None => panic!("Instance oracle with label {} not found", query.label)
                                }
                            },
                            OracleType::Fixed => {
                                match fixed_oracles_mapping.get(&query.label) {
                                    Some(index) => fixed_oracles[*index].query_in_coset(i, query.rotation),
                                    None => panic!("Fixed oracle with label {} not found", query.label)
                                }
                            },
                        }
                    },
                    &|x: F| -x,
                    &|x: F, y: F| x + y,
                    &|x: F, y: F| x * y,
                    &|x: F, y: F| x * y,
                )
            });

            let mut agg = F::zero();
            for (expr_i, theta_i) in
                expressions_at_i.zip(powers_of_theta.iter())
            {
                agg += expr_i * theta_i
            }

            a_extended_coset_domain_evals.push(agg);
        }

        let a = WitnessProverOracle {
            label: format!("lookup_a_{}_poly", lookup_index).to_string(),
            poly: DensePolynomial::from_coefficients_slice(
                &domain.ifft(&a_original_domain_evals),
            ),
            evals: a_original_domain_evals,
            evals_at_coset_of_extended_domain: Some(
                a_extended_coset_domain_evals,
            ),
            queried_rotations: BTreeSet::from([Rotation::curr()]),
            should_permute: false,
        };

        // For now we are supporting just fixed table queries, easily we can extend it to table expressions and
        // we will just repeat what is done for A
        let mut s_original_domain_evals =
            Vec::<F>::with_capacity(domain.size());
        let mut s_extended_coset_domain_evals =
            Vec::<F>::with_capacity(domain.size());

        for i in 0..domain.size() {
            let table_evals_at_i = table_queries.iter().map(|table_query| {
                match table_query.oracle_type {
                    OracleType::Witness => {
                        panic!("Witness not allowed as table query")
                    }
                    OracleType::Instance => {
                        panic!("Instance not allowed as table query")
                    }
                    OracleType::Fixed => {
                        match table_oracles_mapping.get(&table_query.label) {
                            Some(index) => table_oracles[*index].evals[i],
                            None => panic!(
                                "Fixed oracle with label {} not found",
                                table_query.label
                            ),
                        }
                    }
                }
            });

            let mut agg = F::zero();
            for (expr_i, theta_i) in
                table_evals_at_i.zip(powers_of_theta.iter())
            {
                agg += expr_i * theta_i
            }

            s_original_domain_evals.push(agg);
        }

        for i in 0..extended_coset_domain.size() {
            let table_evals_at_i = table_queries.iter().map(|table_query| {
                match table_query.oracle_type {
                    OracleType::Witness => {
                        panic!("Witness not allowed as table query")
                    }
                    OracleType::Instance => {
                        panic!("Instance not allowed as table query")
                    }
                    OracleType::Fixed => {
                        match table_oracles_mapping.get(&table_query.label) {
                            Some(index) => table_oracles[*index]
                                .query_in_coset(i, Rotation::curr()),
                            None => panic!(
                                "Fixed oracle with label {} not found",
                                table_query.label
                            ),
                        }
                    }
                }
            });

            let mut agg = F::zero();
            for (expr_i, theta_i) in
                table_evals_at_i.zip(powers_of_theta.iter())
            {
                agg += expr_i * theta_i
            }

            s_extended_coset_domain_evals.push(agg);
        }

        let s = WitnessProverOracle {
            label: format!("lookup_s_{}_poly", lookup_index).to_string(),
            poly: DensePolynomial::from_coefficients_slice(
                &domain.ifft(&s_original_domain_evals),
            ),
            evals: s_original_domain_evals,
            evals_at_coset_of_extended_domain: Some(
                s_extended_coset_domain_evals,
            ),
            queried_rotations: BTreeSet::from([Rotation::curr()]),
            should_permute: false,
        };

        // We care just about usable rows, rest are used for blinding
        let (mut a_prime_evals, mut s_prime_evals) = permute_for_lookup(
            &a.evals[..usable_rows - 1],
            &s.evals[..usable_rows - 1],
        );

        for _ in usable_rows..=domain.size() {
            a_prime_evals.push(F::rand(zk_rng));
            s_prime_evals.push(F::rand(zk_rng));
        }

        assert_eq!(a_prime_evals.len(), domain.size());
        assert_eq!(s_prime_evals.len(), domain.size());

        let a_prime = WitnessProverOracle {
            label: format!("lookup_a_prime_{}_poly", lookup_index).to_string(),
            poly: DensePolynomial::from_coefficients_slice(
                &domain.ifft(&a_prime_evals),
            ),
            evals_at_coset_of_extended_domain: Some(
                extended_coset_domain.coset_fft(&a_prime_evals),
            ),
            evals: a_prime_evals,
            queried_rotations: BTreeSet::from([
                Rotation::curr(),
                Rotation::prev(), // A'(X) is queried at w^(-1) in lookup argument check
            ]),
            should_permute: false,
        };

        let s_prime = WitnessProverOracle {
            label: format!("lookup_s_prime_{}_poly", lookup_index).to_string(),
            poly: DensePolynomial::from_coefficients_slice(
                &domain.ifft(&s_prime_evals),
            ),
            evals_at_coset_of_extended_domain: Some(
                extended_coset_domain.coset_fft(&s_prime_evals),
            ),
            evals: s_prime_evals,
            queried_rotations: BTreeSet::from([Rotation::curr()]),
            should_permute: false,
        };

        (a, s, a_prime, s_prime)
    }

    pub fn construct_a_and_s_unpermuted_polys_verifier<
        'a,
        PC: HomomorphicCommitment<F>,
    >(
        witness_oracles_mapping: &BTreeMap<String, usize>,
        instance_oracles_mapping: &BTreeMap<String, usize>,
        fixed_oracles_mapping: &BTreeMap<String, usize>,
        table_oracles_mapping: &BTreeMap<String, usize>,
        witness_oracles: &'a [WitnessVerifierOracle<F, PC>],
        instance_oracles: &'a [InstanceVerifierOracle<F>],
        fixed_oracles: &'a [FixedVerifierOracle<F, PC>],
        table_oracles: &'a [FixedVerifierOracle<F, PC>],
        lookup_index: usize,
        lookup_expressions: &[NewExpression<F>],
        table_queries: &[OracleQuery],
        theta: F,                // lookup aggregation expression,
        evaluation_challenge: F, // evaluation_challenge
        omegas: &Vec<F>,
    ) -> (WitnessVerifierOracle<F, PC>, WitnessVerifierOracle<F, PC>) {
        assert_eq!(lookup_expressions.len(), table_queries.len());
        let lookup_arith = lookup_expressions.len();

        let powers_of_theta: Vec<F> =
            successors(Some(F::one()), |theta_i| Some(*theta_i * theta))
                .take(lookup_arith)
                .collect();

        let expression_evals = lookup_expressions.iter().map(|lookup_expr| {
            lookup_expr.evaluate(
                &|x: F| x,
                &|query| match query.oracle_type {
                    OracleType::Witness => {
                        let evaluation_challenge =
                            query.rotation.compute_evaluation_point(
                                evaluation_challenge,
                                omegas,
                            );
                        match witness_oracles_mapping.get(&query.label) {
                            Some(index) => witness_oracles[*index]
                                .query(&evaluation_challenge),
                            None => panic!(
                                "Witness oracle with label {} not found",
                                query.label
                            ),
                        }
                    }
                    OracleType::Instance => {
                        match instance_oracles_mapping.get(&query.label) {
                            Some(index) => instance_oracles[*index]
                                .query(&evaluation_challenge),
                            None => panic!(
                                "Instance oracle with label {} not found",
                                query.label
                            ),
                        }
                    }
                    OracleType::Fixed => {
                        match fixed_oracles_mapping.get(&query.label) {
                            Some(index) => fixed_oracles[*index]
                                .query(&evaluation_challenge),
                            None => panic!(
                                "Fixed oracle with label {} not found",
                                query.label
                            ),
                        }
                    }
                },
                &|x: F| -x,
                &|x: F, y: F| x + y,
                &|x: F, y: F| x * y,
                &|x: F, y: F| x * y,
            )
        });

        let mut agg = F::zero();
        for (expr_i, theta_i) in expression_evals.zip(powers_of_theta.iter()) {
            agg += expr_i * theta_i
        }

        let a = WitnessVerifierOracle::<F, PC> {
            label: format!("lookup_a_{}_poly", lookup_index).to_string(),
            queried_rotations: BTreeSet::from([Rotation::curr()]),
            evals_at_challenges: BTreeMap::from([(evaluation_challenge, agg)]),
            commitment: None,
            should_permute: false,
        };

        let table_evals_at_xi = table_queries.iter().map(|table_query| {
            match table_query.oracle_type {
                OracleType::Witness => {
                    panic!("Witness not allowed as table query")
                }
                OracleType::Instance => {
                    panic!("Instance not allowed as table query")
                }
                OracleType::Fixed => {
                    match table_oracles_mapping.get(&table_query.label) {
                        Some(index) => {
                            table_oracles[*index].query(&evaluation_challenge)
                        }
                        None => panic!(
                            "Fixed oracle with label {} not found",
                            table_query.label
                        ),
                    }
                }
            }
        });

        let mut agg = F::zero();
        for (table_i, theta_i) in table_evals_at_xi.zip(powers_of_theta.iter())
        {
            agg += table_i * theta_i
        }

        let s = WitnessVerifierOracle::<F, PC> {
            label: format!("lookup_s_{}_poly", lookup_index).to_string(),
            queried_rotations: BTreeSet::from([Rotation::curr()]),
            evals_at_challenges: BTreeMap::from([(evaluation_challenge, agg)]),
            commitment: None,
            should_permute: false,
        };

        (a, s)
    }

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
        alpha_powers: &[F],
    ) -> F {
        // we need 3 alphas for subset equality check
        // + 1 to check that A'(w^0) = S'(w^0)
        // + 1 to check well formation of A' and S'
        assert_eq!(alpha_powers.len(), 5);

        let mut num = F::zero();

        num += SubsetEqualityArgument::instantiate_argument_at_omega_i(
            l0_coset_evals,
            q_last_coset_evals,
            q_blind,
            a,
            s,
            a_prime,
            s_prime,
            z,
            beta,
            gamma,
            omega_index,
            &alpha_powers[0..3].to_vec(),
        );

        let a_prime_x = a_prime.query_in_coset(omega_index, Rotation::curr());
        let a_prime_minus_wx =
            a_prime.query_in_coset(omega_index, Rotation::prev());

        let s_prime_x = s_prime.query_in_coset(omega_index, Rotation::curr());

        let q_blind_x = q_blind.query_in_coset(omega_index, Rotation::curr());

        num += alpha_powers[3]
            * l0_coset_evals[omega_index]
            * (a_prime_x - s_prime_x);

        let zk_part = F::one() - (q_last_coset_evals[omega_index] + q_blind_x);
        let a_s_equality_check = a_prime_x - s_prime_x;
        let a_a_prev_equality_check = a_prime_x - a_prime_minus_wx;

        num += alpha_powers[4]
            * zk_part
            * a_s_equality_check
            * a_a_prev_equality_check;

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
        alpha_powers: &[F],
    ) -> F {
        assert_eq!(alpha_powers.len(), 5);

        let mut opening = F::zero();

        opening += SubsetEqualityArgument::open_argument(
            l0_eval,
            q_last_eval,
            q_blind,
            a,
            s,
            a_prime,
            s_prime,
            z,
            beta,
            gamma,
            evaluation_challenge,
            domain,
            &alpha_powers[..3].to_vec(),
        );

        let negative_shifted_evaluation_challenge =
            domain.element(1).inverse().unwrap() * evaluation_challenge;

        let a_prime_xi = a_prime.query(&evaluation_challenge);
        let a_prime_minus_wxi =
            a_prime.query(&negative_shifted_evaluation_challenge);

        let s_prime_xi = s_prime.query(&evaluation_challenge);

        let q_blind_xi = q_blind.query(&evaluation_challenge);

        opening += alpha_powers[3] * l0_eval * (a_prime_xi - s_prime_xi);

        let zk_part = F::one() - (q_last_eval + q_blind_xi);
        let a_s_equality_check = a_prime_xi - s_prime_xi;
        let a_a_prev_equality_check = a_prime_xi - a_prime_minus_wxi;

        opening += alpha_powers[4]
            * zk_part
            * a_s_equality_check
            * a_a_prev_equality_check;

        opening
    }
}

#[cfg(test)]
mod test {
    use std::collections::{BTreeMap, BTreeSet};

    use super::LookupArgument;
    use crate::lookup::subset_equality::SubsetEqualityArgument;
    use crate::oracles::fixed::{FixedProverOracle, FixedVerifierOracle};
    use crate::oracles::rotation::Rotation;
    use crate::oracles::witness::WitnessVerifierOracle;
    use crate::util::compute_vanishing_poly_over_coset;
    use crate::{
        lookup::permute::permute_for_lookup,
        oracles::witness::WitnessProverOracle,
    };

    use crate::commitment::KZG10;
    use ark_bls12_381::{Bls12_381, Fr as F};
    use ark_ff::{batch_inversion, Field, One, UniformRand, Zero};
    use ark_poly::{
        univariate::DensePolynomial, EvaluationDomain, GeneralEvaluationDomain,
    };
    use ark_poly::{Polynomial, UVPolynomial};
    use ark_std::test_rng;

    type PC = KZG10<Bls12_381>;

    #[test]
    fn simple_lookup() {
        let convert_to_field = |x: &[usize]| -> Vec<F> {
            x.iter().map(|&xi| F::from(xi as u64)).collect()
        };

        let domain_size = 16;
        let poly_degree = domain_size - 1;
        let mut rng = test_rng();

        let domain = GeneralEvaluationDomain::<F>::new(domain_size).unwrap();

        let scaling_factor = 4;
        let extended_coset_domain =
            GeneralEvaluationDomain::<F>::new(scaling_factor * domain_size)
                .unwrap();

        let u = 10;

        let dummy_s = 99;

        // table is defined on at most u rows
        // rest can be blinded or filled with some dummy values
        let s = [1, 1, 2, 3, 4, 5, 6, 7, dummy_s, dummy_s];

        // we append dummy s on a values to make them same size
        let a = [1, 1, 1, 2, 2, 2, 3, 6, 7, dummy_s];

        let mut a_evals = convert_to_field(&a);
        let mut s_evals = convert_to_field(&s);

        // now we can blind values
        for _ in u..domain_size {
            a_evals.push(F::rand(&mut rng));
            s_evals.push(F::rand(&mut rng));
        }

        let (mut a_prime_evals, mut s_prime_evals) =
            permute_for_lookup(&a_evals[..u], &s_evals[..u]);

        // now we can blind a_prime and s_prime independently
        for _ in u..domain_size {
            a_prime_evals.push(F::rand(&mut rng));
            s_prime_evals.push(F::rand(&mut rng));
        }

        // sanity check that permutation was correct
        assert_eq!(a_prime_evals[0], s_prime_evals[0]);

        for i in 1..u {
            if a_prime_evals[i] != a_prime_evals[i - 1]
                && a_prime_evals[i] != s_prime_evals[i]
            {
                panic!("Something wrong")
            }
        }

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
        let alpha_powers = vec![
            F::one(),
            alpha,
            alpha * alpha,
            alpha * alpha * alpha,
            alpha * alpha * alpha * alpha,
        ];

        let mut num_evals =
            Vec::<F>::with_capacity(extended_coset_domain.size());
        for i in 0..extended_coset_domain.size() {
            let ni = LookupArgument::instantiate_argument_at_omega_i(
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

        let num = DensePolynomial::from_coefficients_slice(
            &extended_coset_domain.coset_ifft(&num_evals),
        );
        let zh_dense: DensePolynomial<F> = domain.vanishing_polynomial().into();

        let q = &num / &zh_dense;
        assert_eq!(num, &q * &zh_dense);

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

        let omega_minus_1 = domain.element(1).inverse().unwrap();
        let negative_rotated_challenge = evaluation_challenge * omega_minus_1;
        let a_prime = WitnessVerifierOracle {
            label: "a_prime".to_string(),
            queried_rotations: BTreeSet::from([
                Rotation::curr(),
                Rotation::prev(),
            ]),
            evals_at_challenges: BTreeMap::from([
                (
                    evaluation_challenge,
                    a_prime_poly.evaluate(&evaluation_challenge),
                ),
                (
                    negative_rotated_challenge,
                    a_prime_poly.evaluate(&negative_rotated_challenge),
                ),
            ]),
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

        let opening = LookupArgument::open_argument::<PC>(
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
