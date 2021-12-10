use crate::link::{PESubspaceSnark, SubspaceSnark};
use ark_ec::{AffineCurve, PairingEngine, ProjectiveCurve};
use ark_ff::PrimeField;

use super::{PreparedVerifyingKey, Proof, VerifyingKey};

use ark_relations::r1cs::{Result as R1CSResult, SynthesisError};

use ark_std::vec;
use ark_std::vec::Vec;
use core::ops::{AddAssign, Neg};

/// Prepare the verifying key `vk` for use in proof verification.
pub fn prepare_verifying_key<E: PairingEngine>(vk: &VerifyingKey<E>) -> PreparedVerifyingKey<E> {
    PreparedVerifyingKey {
        vk: vk.clone(),
        alpha_g1_beta_g2: E::pairing(vk.alpha_g1, vk.beta_g2),
        gamma_g2_neg_pc: vk.gamma_g2.neg().into(),
        delta_g2_neg_pc: vk.delta_g2.neg().into(),
    }
}

pub fn verify_link_proof<E: PairingEngine>(vk: &VerifyingKey<E>, proof: &Proof<E>) -> bool {
    let commitments = vec![proof.link_d.into_projective(), proof.d.into_projective()];
    PESubspaceSnark::<E>::verify(
        &vk.link_pp,
        &vk.link_vk,
        &commitments
            .iter()
            .map(|p| p.into_affine())
            .collect::<Vec<_>>(),
        &proof.link_pi,
    )
}

/// Verify a Groth16 proof `proof` against the prepared verification key `pvk`,
/// with respect to the instance `public_inputs`.
pub fn verify_proof<E: PairingEngine>(
    pvk: &PreparedVerifyingKey<E>,
    proof: &Proof<E>,
) -> R1CSResult<bool> {
    // TODO: Return error indicating what failed rather than a boolean
    let link_verified = verify_link_proof(&pvk.vk, proof);
    if !link_verified {
        return Ok(false);
    }
    let qap = E::miller_loop(
        [
            (proof.a.into(), proof.b.into()),
            (proof.c.into(), pvk.delta_g2_neg_pc.clone()),
            (proof.d.into(), pvk.gamma_g2_neg_pc.clone()),
        ]
        .iter(),
    );

    let test = E::final_exponentiation(&qap).ok_or(SynthesisError::UnexpectedIdentity)?;

    Ok(test == pvk.alpha_g1_beta_g2)
}

pub fn verify_commitment<E: PairingEngine>(
    pvk: &PreparedVerifyingKey<E>,
    proof: &Proof<E>,
    public_inputs: &[E::Fr],
    v: &E::Fr,
    link_v: &E::Fr,
) -> Result<bool, SynthesisError> {
    if (public_inputs.len() + 1) != pvk.vk.gamma_abc_g1.len() {
        return Err(SynthesisError::MalformedVerifyingKey);
    }
    if (public_inputs.len() + 2) != pvk.vk.link_bases.len() {
        return Err(SynthesisError::MalformedVerifyingKey);
    }

    let mut g_ic = pvk.vk.gamma_abc_g1[0].into_projective();
    for (i, b) in public_inputs.iter().zip(pvk.vk.gamma_abc_g1.iter().skip(1)) {
        g_ic.add_assign(&b.mul(i.into_repr()));
    }
    g_ic.add_assign(&pvk.vk.eta_gamma_inv_g1.mul(v.into_repr()));

    let mut g_link = pvk.vk.link_bases[0].into_projective();
    for (i, b) in public_inputs.iter().zip(pvk.vk.link_bases.iter().skip(1)) {
        g_link.add_assign(&b.mul(i.into_repr()));
    }
    g_link.add_assign(&pvk.vk.link_bases.last().unwrap().mul(link_v.into_repr()));

    Ok(proof.d == g_ic.into_affine() && proof.link_d == g_link.into_affine())
}
