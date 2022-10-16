pub mod individual;
mod playground;

/*
    (1 - (q_last + q_blind)) * zp(wX) * Product_i(oracle(x) + sigma(x) + gamma) NOTE: second part is symmetrical
    degree of this will always be:
    2n - 2 + num_of_oracles * n - num_of_oracles

    so for num_of_oracles = 2
        (1 - (q_last + q_blind)) * zp(wX) * (oracle1(x) + sigma1(x) + gamma) * (oracle2(x) + sigma2(x) + gamma)
        4n - 4

    for classic plonk arith we have qm * a * b - zh = 3n - 3 - n = 2n - 3
*/

/*

set u = 6

we want a * b - c = 0



    a       b       c
------------------------
1   a1      b1      c1
------------------------
2
------------------------
3
------------------------
4
------------------------
5
------------------------
6
------------------------
7
------------------------
8

*/

// pub fn construct_product_rule<F: PrimeField, PC: HomomorphicCommitment<F>>(
//     q_last: &FixedOracle<F, PC>, //TODO: THIS CAN BE REPRESENTED AS Lu(X)
//     q_blind: &FixedOracle<F, PC>,
//     z: &impl WitnessOracle<F>,
//     permutation_oracles: &[FixedOracle<F, PC>],
//     witness_oracles: &[impl WitnessOracle<F>],
//     x_poly: InstanceOracle<F>, // TODO: Consider better X handling
//     deltas: &[F],
//     beta: F,
//     gamma: F,
// ) -> NewExpression<F> {
//     let q_last_exp: NewExpression<F> = OracleQuery {
//         label: q_last.get_label(),
//         rotation: Rotation::curr(),
//         oracle_type: OracleType::Fixed,
//     }
//     .into();

//     let q_blind_expr: NewExpression<F> = OracleQuery {
//         label: q_blind.get_label(),
//         rotation: Rotation::curr(),
//         oracle_type: OracleType::Fixed,
//     }
//     .into();

//     let z_x: NewExpression<F> = OracleQuery {
//         label: z.get_label(),
//         rotation: Rotation::curr(),
//         oracle_type: OracleType::Witness,
//     }
//     .into();

//     let z_wx: NewExpression<F> = OracleQuery {
//         label: z.get_label(),
//         rotation: Rotation::next(),
//         oracle_type: OracleType::Witness,
//     }
//     .into();

//     let x_expr: NewExpression<F> = OracleQuery {
//         label: x_poly.get_label(),
//         rotation: Rotation::curr(),
//         oracle_type: OracleType::Instance,
//     }
//     .into();

//     let permutation_queries = permutation_oracles
//         .iter()
//         .map(|sigma| {
//             OracleQuery {
//                 label: sigma.get_label(),
//                 rotation: Rotation::curr(),
//                 oracle_type: OracleType::Fixed,
//             }
//             .into()
//         })
//         .collect::<Vec<NewExpression<F>>>();

//     let witness_queries = witness_oracles
//         .iter()
//         .map(|w| {
//             OracleQuery {
//                 label: w.get_label(),
//                 rotation: Rotation::curr(),
//                 oracle_type: OracleType::Witness,
//             }
//             .into()
//         })
//         .collect::<Vec<NewExpression<F>>>();

//     let delta_consts: Vec<NewExpression<F>> = deltas
//         .iter()
//         .map(|&delta| NewExpression::Constant(delta))
//         .collect();

//     let beta_const: NewExpression<F> = NewExpression::Constant(beta);
//     let gamma_const: NewExpression<F> = NewExpression::Constant(gamma);

//     let zk_part =
//         NewExpression::Constant(F::one()) - (q_last_exp + q_blind_expr);

//     let product_part = {
//         let mut lhs = z_wx;
//         for (w_i, sigma_i) in
//             witness_queries.iter().zip(permutation_queries.iter())
//         {
//             lhs = lhs
//                 + (w_i.clone()
//                     + beta_const.clone() * sigma_i.clone()
//                     + gamma_const.clone());
//         }

//         let mut rhs = z_x;
//         for (w_i, delta_i) in witness_queries.iter().zip(delta_consts.iter()) {
//             rhs = rhs
//                 + (w_i.clone()
//                     + beta_const.clone() * delta_i.clone() * x_expr.clone()
//                     + gamma_const.clone());
//         }

//         lhs - rhs
//     };

//     zk_part * product_part
// }
