use ark_ec::pairing::Pairing;
use ark_ff::PrimeField;
use ark_relations::r1cs::ConstraintSynthesizer;
use ark_serialize::*;
use ark_std::{vec::Vec, rand::{RngCore, CryptoRng}};

#[derive(Clone, Debug, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
/// The randomzier
pub struct Randomizer<E: Pairing> {
    /// Randomizer `r` in scaler.
    pub r: E::ScalarField,
    /// Randomizer `s` in scaler.
    pub s: E::ScalarField,
    /// The `P` element in `G1`
    pub p: E::G1Affine,
    /// The `Q` element in `G1`
    pub q: E::G1Affine,
}

impl<E: Pairing> Default for Randomizer<E> {
    fn default() -> Self {
        Self {
            r: E::ScalarField::default(),
            s: E::ScalarField::default(),
            p: E::G1Affine::default(),
            q: E::G1Affine::default(),
        }
    }
}

/// A proof in the Groth16 SNARK.
#[derive(Clone, Debug, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct Proof<E: Pairing> {
    /// The `A` element in `G1`.
    pub a: E::G1Affine,
    /// The `B` element in `G2`.
    pub b: E::G2Affine,
    /// The `C` element in `G1`.
    pub c: E::G1Affine,
}

impl<E: Pairing> Default for Proof<E> {
    fn default() -> Self {
        Self {
            a: E::G1Affine::default(),
            b: E::G2Affine::default(),
            c: E::G1Affine::default(),
        }
    }
}

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

/// A verification key in the Groth16 SNARK.
#[derive(Clone, Debug, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct VerifyingKey<E: Pairing> {
    /// The `alpha * G`, where `G` is the generator of `E::G1`.
    pub alpha_g1: E::G1Affine,
    /// The `alpha * H`, where `H` is the generator of `E::G2`.
    pub beta_g2: E::G2Affine,
    /// The `gamma * H`, where `H` is the generator of `E::G2`.
    pub gamma_g2: E::G2Affine,
    /// The `delta * H`, where `H` is the generator of `E::G2`.
    pub delta_g2: E::G2Affine,
    /// The `gamma^{-1} * (beta * a_i + alpha * b_i + c_i) * H`, where `H` is the generator of `E::G1`.
    pub gamma_abc_g1: Vec<E::G1Affine>,
}

impl<E: Pairing> Default for VerifyingKey<E> {
    fn default() -> Self {
        Self {
            alpha_g1: E::G1Affine::default(),
            beta_g2: E::G2Affine::default(),
            gamma_g2: E::G2Affine::default(),
            delta_g2: E::G2Affine::default(),
            gamma_abc_g1: Vec::new(),
        }
    }
}

/// Preprocessed verification key parameters that enable faster verification
/// at the expense of larger size in memory.
#[derive(Clone, Debug, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct PreparedVerifyingKey<E: Pairing> {
    /// The unprepared verification key.
    pub vk: VerifyingKey<E>,
    /// The element `e(alpha * G, beta * H)` in `E::GT`.
    pub alpha_g1_beta_g2: E::TargetField,
    /// The element `- gamma * H` in `E::G2`, prepared for use in pairings.
    pub gamma_g2_neg_pc: E::G2Prepared,
    /// The element `- delta * H` in `E::G2`, prepared for use in pairings.
    pub delta_g2_neg_pc: E::G2Prepared,
}

impl<E: Pairing> From<PreparedVerifyingKey<E>> for VerifyingKey<E> {
    fn from(other: PreparedVerifyingKey<E>) -> Self {
        other.vk
    }
}

impl<E: Pairing> From<VerifyingKey<E>> for PreparedVerifyingKey<E> {
    fn from(other: VerifyingKey<E>) -> Self {
        crate::prepare_verifying_key(&other)
    }
}

impl<E: Pairing> Default for PreparedVerifyingKey<E> {
    fn default() -> Self {
        Self {
            vk: VerifyingKey::default(),
            alpha_g1_beta_g2: E::TargetField::default(),
            gamma_g2_neg_pc: E::G2Prepared::default(),
            delta_g2_neg_pc: E::G2Prepared::default(),
        }
    }
}

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

/// The prover key for for the Groth16 zkSNARK.
#[derive(Clone, Debug, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct ProvingKey<E: Pairing> {
    /// The underlying verification key.
    pub vk: VerifyingKey<E>,
    /// The element `beta * G` in `E::G1`.
    pub beta_g1: E::G1Affine,
    /// The element `delta * G` in `E::G1`.
    pub delta_g1: E::G1Affine,
    /// The element `delta * G` in `E::G2`.
    pub delta_g2: E::G2Affine,
    /// The elements `a_i * G` in `E::G1`.
    pub a_query: Vec<E::G1Affine>,
    /// The elements `b_i * G` in `E::G1`.
    pub b_g1_query: Vec<E::G1Affine>,
    /// The elements `b_i * H` in `E::G2`.
    pub b_g2_query: Vec<E::G2Affine>,
    /// The elements `h_i * G` in `E::G1`.
    pub h_query: Vec<E::G1Affine>,
    /// The elements `l_i * G` in `E::G1`.
    pub l_query: Vec<E::G1Affine>,
}

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

/// The basic functionality for a PolymorphicSNARK
pub trait PolymorphicSNARK<F: PrimeField> {
    /// The information required by the prover to produce a proof for a specific
    /// circuit *C*.
    type ProvingKey: Clone + CanonicalSerialize + CanonicalDeserialize;

    /// The information required by the verifier to check a proof for a specific
    /// circuit *C*.
    type VerifyingKey: Clone + CanonicalSerialize + CanonicalDeserialize;

    /// The randomizer output by the prover
    type Randomizer: Clone + CanonicalSerialize + CanonicalDeserialize;

    /// The proof output by the prover.
    type Proof: Clone + CanonicalSerialize + CanonicalDeserialize;

    /// This contains the verification key, but preprocessed to enable faster
    /// verification.
    type ProcessedVerifyingKey: Clone + CanonicalSerialize + CanonicalDeserialize;

    /// Errors encountered during setup, proving, or verification.
    type Error: 'static + ark_std::error::Error;

    /// Takes in a description of a computation (specified in R1CS constraints),
    /// and samples proving and verification keys for that circuit.
    fn circuit_specific_setup<C: ConstraintSynthesizer<F>, R: RngCore + CryptoRng>(
        circuit: C,
        rng: &mut R,
    ) -> Result<(Self::ProvingKey, Self::VerifyingKey), Self::Error>;

    /// Generates randomizer
    fn rndgen<R: RngCore>(pk: &Self::ProvingKey, rng: &mut R) -> Result<Self::Randomizer, Self::Error>;

    /// Generates a proof of satisfaction of the arithmetic circuit C (specified
    /// as R1CS constraints).
    fn prove<C: ConstraintSynthesizer<F>>(
        circuit_pk: &Self::ProvingKey,
        circuit: C,
        rnd: &Self::Randomizer
    ) -> Result<Self::Proof, Self::Error>;

    /// Preprocesses `circuit_vk` to enable faster verification.
    fn process_vk(
        circuit_vk: &Self::VerifyingKey,
    ) -> Result<Self::ProcessedVerifyingKey, Self::Error>;

    /// Checks that `proof` is a valid proof of the satisfaction of circuit
    /// encoded in `circuit_pvk`, with respect to the public input `public_input`,
    /// specified as R1CS constraints.
    fn verify_with_processed_vk(
        circuit_pvk: &Self::ProcessedVerifyingKey,
        public_input: &[F],
        proof: &Self::Proof,
        rnd: &Self::Randomizer
    ) -> Result<bool, Self::Error>;

    /// Checks that all `proofs` are all distinct 
    fn compare_all_proofs(
        proofs: &Vec<Self::Proof>
    ) -> Result<bool, Self::Error>;
}

/// A SNARK with (only) circuit-specific setup.
pub trait CircuitSpecificSetupPolymorphicSNARK<F: PrimeField>: PolymorphicSNARK<F> {
    /// The setup algorithm for circuit-specific SNARKs. By default, this
    /// just invokes `<Self as SNARK<F>>::circuit_specific_setup(...)`.
    fn setup<C: ConstraintSynthesizer<F>, R: RngCore + CryptoRng>(
        circuit: C,
        rng: &mut R,
    ) -> Result<(Self::ProvingKey, Self::VerifyingKey), Self::Error> {
        <Self as PolymorphicSNARK<F>>::circuit_specific_setup(circuit, rng)
    }
}
