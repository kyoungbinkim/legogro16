use crate::link::{PESubspaceSnark, SubspaceSnark};
use ark_ec::{AffineCurve, PairingEngine, ProjectiveCurve};
use ark_ff::PrimeField;

use super::{PreparedVerifyingKey, Proof, VerifyingKey};

use ark_relations::r1cs::SynthesisError;

use crate::error::Error;
use ark_ec::msm::VariableBaseMSM;
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

/// Prepare proof inputs for use with [`verify_proof_with_prepared_inputs`], wrt the prepared
/// verification key `pvk` and instance public inputs.
pub fn prepare_inputs<E: PairingEngine>(
    pvk: &PreparedVerifyingKey<E>,
    public_inputs: &[E::Fr],
) -> crate::Result<E::G1Projective> {
    if (public_inputs.len() + 1) != pvk.vk.gamma_abc_g1.len() {
        return Err(SynthesisError::MalformedVerifyingKey).map_err(|e| e.into());
    }

    let mut g_ic = pvk.vk.gamma_abc_g1[0].into_projective();
    for (i, b) in public_inputs.iter().zip(pvk.vk.gamma_abc_g1.iter().skip(1)) {
        g_ic.add_assign(&b.mul(i.into_repr()));
    }

    Ok(g_ic)
}

/// Verify the proof of the Subspace Snark on the equality of openings of cp_link and proof.d
pub fn verify_link_proof<E: PairingEngine>(
    vk: &VerifyingKey<E>,
    proof: &Proof<E>,
) -> crate::Result<()> {
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
    .map_err(|e| e.into())
}

/// Verify a LegoGroth16 proof `proof` against the prepared verification key `pvk`
pub fn verify_proof<E: PairingEngine>(
    pvk: &PreparedVerifyingKey<E>,
    proof: &Proof<E>,
    public_inputs: Option<&[E::Fr]>,
) -> crate::Result<()> {
    verify_link_proof(&pvk.vk, proof)?;
    let mut d = proof.d.into_projective();
    if let Some(inputs) = public_inputs {
        d.add_assign(prepare_inputs(pvk, inputs)?);
    }

    let qap = E::miller_loop(
        [
            (proof.a.into(), proof.b.into()),
            (proof.c.into(), pvk.delta_g2_neg_pc.clone()),
            (d.into_affine().into(), pvk.gamma_g2_neg_pc.clone()),
        ]
        .iter(),
    );

    let test = E::final_exponentiation(&qap).ok_or(SynthesisError::UnexpectedIdentity)?;

    if test != pvk.alpha_g1_beta_g2 {
        return Err(Error::InvalidProof);
    }
    Ok(())
}

/// Redact public inputs from the commitment in the proof such that commitment opens only to the witnesses
pub fn get_commitment_to_witnesses<E: PairingEngine>(
    vk: &VerifyingKey<E>,
    proof: &Proof<E>,
    public_inputs: &[E::Fr],
) -> crate::Result<E::G1Affine> {
    let inputs = public_inputs
        .into_iter()
        .map(|p| p.into_repr())
        .collect::<Vec<_>>();
    if inputs.len() > vk.link_bases.len() {
        return Err(Error::VectorLongerThanExpected(
            inputs.len(),
            vk.link_bases.len(),
        ));
    }
    let mut g_link = vk.link_bases[0].into_projective();
    g_link.add_assign(VariableBaseMSM::multi_scalar_mul(
        &vk.link_bases[1..],
        &inputs,
    ));
    Ok((proof.link_d.into_projective() - g_link).into_affine())
}
