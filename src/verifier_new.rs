use std::ops::AddAssign;
use ark_ec::{AffineCurve, PairingEngine, ProjectiveCurve};
use ark_ff::PrimeField;
use ark_relations::r1cs::SynthesisError;
use crate::{Proof, VerifyingKey};

/// Redact public inputs from the commitment in the proof such that commitment is only to the witnesses
pub fn get_commitment_to_witnesses<E: PairingEngine>(
    vk: &VerifyingKey<E>,
    proof: &Proof<E>,
    public_inputs: &[E::Fr],
) -> Result<E::G1Affine, SynthesisError> {
    let mut g_link = vk.link_bases[0].into_projective();
    for (i, b) in public_inputs.iter().zip(vk.link_bases.iter().skip(1)) {
        g_link.add_assign(&b.mul(i.into_repr()));
    }
    Ok((proof.link_d.into_projective() - g_link).into_affine())
}

/// Check that the commitments in the proof open to the public inputs and the witnesses but with different
/// bases and randomness
pub fn verify_commitment_new<E: PairingEngine>(
    vk: &VerifyingKey<E>,
    proof: &Proof<E>,
    public_inputs: &[E::Fr],
    witnesses_expected_in_commitment: &[E::Fr],
    v: &E::Fr,
    link_v: &E::Fr,
) -> Result<bool, SynthesisError> {

    let mut g_ic = vk.gamma_abc_g1[0].into_projective();
    for (i, b) in public_inputs.iter().chain(witnesses_expected_in_commitment.iter()).zip(vk.gamma_abc_g1.iter().skip(1)) {
        g_ic.add_assign(&b.mul(i.into_repr()));
    }
    g_ic.add_assign(&vk.eta_gamma_inv_g1.mul(v.into_repr()));

    let mut g_link = vk.link_bases[0].into_projective();
    for (i, b) in public_inputs.iter().chain(witnesses_expected_in_commitment.iter()).zip(vk.link_bases.iter().skip(1)) {
        g_link.add_assign(&b.mul(i.into_repr()));
    }
    g_link.add_assign(&vk.link_bases.last().unwrap().mul(link_v.into_repr()));

    let r1 = proof.d == g_ic.into_affine();
    let r2 = proof.link_d == g_link.into_affine();
    // println!("{} {}", r1, r2);
    // TODO: Return error indicating which check failed
    Ok(r1 && r2)
}
