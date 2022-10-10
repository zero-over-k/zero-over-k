//! Useful commitment stuff
use std::ops::Add;

use ark_ec::{msm::VariableBaseMSM, AffineCurve, PairingEngine};
use ark_ff::{One, PrimeField, Zero};
use ark_poly::univariate::DensePolynomial;
use ark_poly_commit::{
    sonic_pc::SonicKZG10, PCRandomness, PolynomialCommitment,
};

/// A homomorphic polynomial commitment
pub trait HomomorphicCommitment<F>:
    PolynomialCommitment<F, DensePolynomial<F>>
where
    F: PrimeField,
{
    /// Combine a linear combination of homomorphic commitments
    fn msm(commitments: &[Self::Commitment], scalars: &[F])
        -> Self::Commitment;

    fn neg_com(commitment: &Self::Commitment) -> Self::Commitment;

    fn scale_com(commitment: &Self::Commitment, scalar: F) -> Self::Commitment;

    fn add(c1: &Self::Commitment, c2: &Self::Commitment) -> Self::Commitment;

    fn zero_comm() -> Self::Commitment;

    fn is_zero(c: &Self::Commitment) -> bool;

    fn eq_cm(c1: &Self::Commitment, c2: &Self::Commitment) -> bool;

    fn scale_rand(randomness: &Self::Randomness, scalar: F)
        -> Self::Randomness;

    fn add_rands(
        a: &Self::Randomness,
        b: &Self::Randomness,
    ) -> Self::Randomness;

    fn add_assign_rand(a: &mut Self::Randomness, b: &Self::Randomness);
}

/// The Default KZG-style commitment scheme
pub type KZG10<E> = SonicKZG10<E, DensePolynomial<<E as PairingEngine>::Fr>>;
/// A single KZG10 commitment
pub type KZG10Commitment<E> = <KZG10<E> as PolynomialCommitment<
    <E as PairingEngine>::Fr,
    DensePolynomial<<E as PairingEngine>::Fr>,
>>::Commitment;

impl<'a, E> HomomorphicCommitment<E::Fr> for KZG10<E>
where
    E: PairingEngine,
{
    fn msm(
        commitments: &[Self::Commitment],
        scalars: &[E::Fr],
    ) -> Self::Commitment {
        let scalars_repr = scalars
            .iter()
            .map(<E::Fr as PrimeField>::into_repr)
            .collect::<Vec<_>>();

        let points_repr = commitments.iter().map(|c| c.0).collect::<Vec<_>>();

        ark_poly_commit::kzg10::Commitment::<E>(
            VariableBaseMSM::multi_scalar_mul(&points_repr, &scalars_repr)
                .into(),
        )
    }

    fn neg_com(c: &Self::Commitment) -> Self::Commitment {
        ark_poly_commit::kzg10::Commitment::<E>(c.0.mul(-E::Fr::one()).into())
    }

    fn scale_com(
        commitment: &Self::Commitment,
        scalar: E::Fr,
    ) -> Self::Commitment {
        ark_poly_commit::kzg10::Commitment::<E>(commitment.0.mul(scalar).into())
    }

    fn add(c1: &Self::Commitment, c2: &Self::Commitment) -> Self::Commitment {
        ark_poly_commit::kzg10::Commitment::<E>(c1.0 + c2.0)
    }

    fn zero_comm() -> Self::Commitment {
        ark_poly_commit::kzg10::Commitment::<E>(E::G1Affine::zero())
    }

    fn is_zero(c: &Self::Commitment) -> bool {
        c.0.is_zero()
    }

    fn eq_cm(c1: &Self::Commitment, c2: &Self::Commitment) -> bool {
        c1.0 == c2.0
    }

    fn scale_rand(
        randomness: &Self::Randomness,
        scalar: E::Fr,
    ) -> Self::Randomness {
        let mut rand = Self::Randomness::empty();
        rand.blinding_polynomial = &randomness.blinding_polynomial * scalar;
        rand
    }

    fn add_rands(
        a: &Self::Randomness,
        b: &Self::Randomness,
    ) -> Self::Randomness {
        a.clone() + b
    }

    fn add_assign_rand(a: &mut Self::Randomness, b: &Self::Randomness) {
        a.blinding_polynomial += &b.blinding_polynomial
    }
}
