use ark_ff::PrimeField;

use crate::{vo::new_expression::NewExpression, oracles::{fixed::FixedOracle, traits::{ConcreteOracle, WitnessOracle}, query::{OracleQuery, OracleType}, rotation::Rotation, instance::InstanceOracle}, commitment::HomomorphicCommitment};

/// This module constructs one zero knowledge adjusted permutation check 
/// (1 - (q_blind + q_last)) * (z(wX) * product_0,m-1 (vi(X) + beta*sigma_i(X) + gamma) - z(X) * product_0,m-1 (vi(X) + beta*sigma^i*X + gamma))
/// It isn't aware of outer context where splitting, copying across aggregation polynomials, beginning and ending checks are happening 
pub fn construct_product_rule<F: PrimeField, PC: HomomorphicCommitment<F>>(
    q_last: &FixedOracle<F, PC>, //TODO: THIS CAN BE REPRESENTED AS Lu(X)
    q_blind: &FixedOracle<F, PC>, 
    z: &impl WitnessOracle<F>,
    permutation_oracles: &[FixedOracle<F, PC>],
    witness_oracles: &[impl WitnessOracle<F>],
    x_poly: InstanceOracle<F>, // TODO: Consider better X handling
    deltas: &[F], 
    beta: F, 
    gamma: F
) -> NewExpression<F>
{
    let q_last_exp: NewExpression<F> = OracleQuery {
        label: q_last.get_label(),
        rotation: Rotation::curr(),
        oracle_type: OracleType::Fixed,
    }.into();

    let q_blind_expr: NewExpression<F> = OracleQuery {
        label: q_blind.get_label(),
        rotation: Rotation::curr(),
        oracle_type: OracleType::Fixed,
    }.into();

    let z_x: NewExpression<F> = OracleQuery {
        label: z.get_label(),
        rotation: Rotation::curr(),
        oracle_type: OracleType::Witness,
    }.into();

    let z_wx: NewExpression<F> = OracleQuery {
        label: z.get_label(),
        rotation: Rotation::next(),
        oracle_type: OracleType::Witness,
    }.into();

    let x_expr: NewExpression<F> = OracleQuery {
        label: x_poly.get_label(),
        rotation: Rotation::curr(),
        oracle_type: OracleType::Instance,
    }.into();

    let permutation_queries = permutation_oracles.iter().map(|sigma| {
        OracleQuery {
            label: sigma.get_label(),
            rotation: Rotation::curr(),
            oracle_type: OracleType::Fixed,
        }.into()
    }).collect::<Vec<NewExpression<F>>>();

    let witness_queries = witness_oracles.iter().map(|w| {
        OracleQuery {
            label: w.get_label(),
            rotation: Rotation::curr(),
            oracle_type: OracleType::Witness,
        }.into()
    }).collect::<Vec<NewExpression<F>>>();

    let delta_consts: Vec<NewExpression<F>> = deltas.iter().map(|&delta| NewExpression::Constant(delta)).collect();

    let beta_const: NewExpression<F> = NewExpression::Constant(beta);
    let gamma_const: NewExpression<F> = NewExpression::Constant(gamma);

    let zk_part= NewExpression::Constant(F::one()) - (q_last_exp + q_blind_expr);

    let product_part = { 
        let mut lhs = z_wx;
        for (w_i, sigma_i) in witness_queries.iter().zip(permutation_queries.iter()) {
            lhs = lhs + (w_i.clone() + beta_const.clone() * sigma_i.clone() + gamma_const.clone());
        }

        let mut rhs = z_x;
        for (w_i, delta_i) in witness_queries.iter().zip(delta_consts.iter()) {
            rhs = rhs + (w_i.clone() + beta_const.clone() * delta_i.clone() * x_expr.clone() + gamma_const.clone());
        }

        lhs - rhs
    };

    zk_part * product_part
}


#[cfg(test)]
mod test {
    use ark_ff::{Zero, One, UniformRand, Field};
    use ark_poly::{GeneralEvaluationDomain, EvaluationDomain, univariate::DensePolynomial, UVPolynomial};

    use ark_bls12_381::Fr as F;
    use ark_std::test_rng;

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

        let k = 4; 
        let domain_size = 8; 
        let domain = GeneralEvaluationDomain::<F>::new(domain_size).unwrap();

        let t = 2; 
        let u = domain_size - t - 1;

        let q_blind_evals = [F::zero(), F::zero(), F::zero(), F::zero(), F::zero(), F::zero(), F::one(), F::one()];
        let q_last_evals = [F::zero(), F::zero(), F::zero(), F::zero(), F::zero(), F::one(), F::zero(), F::zero()];

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
            dummy 
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
            dummy 
        ];


        let a = DensePolynomial::<F>::from_coefficients_slice(&domain.ifft(&a_evals));
        let b = DensePolynomial::<F>::from_coefficients_slice(&domain.ifft(&a_evals));

        let q_last = DensePolynomial::<F>::from_coefficients_slice(&domain.ifft(&q_last_evals));
        let q_blind = DensePolynomial::<F>::from_coefficients_slice(&domain.ifft(&q_blind_evals));


        let sigma_1 = DensePolynomial::<F>::from_coefficients_slice(&domain.ifft(&sigma_1_evals));
        let sigma_2 = DensePolynomial::<F>::from_coefficients_slice(&domain.ifft(&sigma_2_evals));

        let beta = F::rand(&mut rng); 
        let gamma = F::rand(&mut rng); 

        // z = [1, a0/b0, z1 * a1/b1, z2 * a2/b2, z3 * a3/b3, z4 * a4/b4, blind, blind]
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

            z_prev *= (nom * denom.inverse().unwrap());
            z_evals.push(z_prev);
        }

        assert_eq!(z_evals[u], F::one());
        // push 2 blinds
        z_evals.push(F::rand(&mut rng));
        z_evals.push(F::rand(&mut rng));

        let z_poly = DensePolynomial::<F>::from_coefficients_slice(&domain.ifft(&z_evals));

        // tmp just push first z_eval for easier querying z[wX] in last w
        z_evals.push(F::one());

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


    }
}