use ark_ec::msm::VariableBaseMSM;
use ark_ec::{AffineCurve, PairingEngine, ProjectiveCurve};
use ark_ff::PrimeField;
use ark_groth16::Proof;
use ark_std::{cfg_iter, format, rand::Rng, string::ToString, vec::Vec};

#[cfg(feature = "parallel")]
use rayon::prelude::*;

use crate::aggregation::error::AggregationError;
use crate::aggregation::groth16::verifier::verify_tipp_mipp;
use crate::aggregation::groth16::{aggregate_proofs as g16_aggregate_proofs, AggregateProof};
use crate::aggregation::pairing_check::PairingCheck;
use crate::aggregation::srs::{ProverSRS, VerifierSRS};
use crate::aggregation::transcript::Transcript;
use crate::aggregation::utils::{aggregate_public_inputs, powers, sum_of_powers};
use crate::{PreparedVerifyingKey, Proof as LegoProof};

/// Since `proof.D` (commitment to witnesses) is needed for doing a Schnorr proof of knowledge and equality
/// when not using CP_link Snark, `proof.D` does not need to be used in an IPA and thus aggregation protocol
/// for Groth16 can be used with slight modification.

pub fn aggregate_proofs<E: PairingEngine, T: Transcript>(
    srs: &ProverSRS<E>,
    transcript: &mut T,
    proofs: &[LegoProof<E>],
) -> Result<(AggregateProof<E>, Vec<E::G1Affine>), AggregationError> {
    let mut g16_proofs = Vec::with_capacity(proofs.len());
    let mut d = Vec::with_capacity(proofs.len());
    for i in 0..proofs.len() {
        g16_proofs.push(Proof {
            a: proofs[i].a,
            b: proofs[i].b,
            c: proofs[i].c,
        });
        d.push(proofs[i].d);
    }
    Ok((g16_aggregate_proofs(srs, transcript, &g16_proofs)?, d))
}

pub fn verify_aggregate_proof<E: PairingEngine, R: Rng, T: Transcript>(
    ip_verifier_srs: &VerifierSRS<E>,
    pvk: &PreparedVerifyingKey<E>,
    public_inputs: &[Vec<E::Fr>],
    proof: &AggregateProof<E>,
    d: &[E::G1Affine],
    rng: &mut R,
    mut transcript: &mut T,
    pairing_check: Option<&mut PairingCheck<E>>,
) -> Result<(), AggregationError> {
    proof.parsing_check()?;
    for pub_input in public_inputs {
        if (pub_input.len() + 1) > pvk.vk.gamma_abc_g1.len() {
            return Err(AggregationError::MalformedVerifyingKey);
        }
    }

    if public_inputs.len() != proof.tmipp.gipa.nproofs as usize {
        return Err(AggregationError::InvalidProof(format!(
            "public inputs len {} != number of proofs {}",
            public_inputs.len(),
            proof.tmipp.gipa.nproofs
        )));
    }

    // Random linear combination of proofs
    transcript.append(b"AB-commitment", &proof.com_ab);
    transcript.append(b"C-commitment", &proof.com_c);

    let r = transcript.challenge_scalar::<E::Fr>(b"r-random-fiatshamir");

    let mut c = PairingCheck::new_using_rng(rng);
    let mut checker = pairing_check.unwrap_or_else(|| &mut c);

    let ver_srs_proj = ip_verifier_srs.to_projective();
    verify_tipp_mipp::<E, T>(
        &ver_srs_proj,
        proof,
        &r, // we give the extra r as it's not part of the proof itself - it is simply used on top for the groth16 aggregation
        &mut transcript,
        &mut checker,
    )?;

    let mut source1 = Vec::with_capacity(3);
    let mut source2 = Vec::with_capacity(3);

    let r_powers = powers(public_inputs.len(), &r);
    let r_sum = sum_of_powers::<E::Fr>(public_inputs.len(), &r);

    // Check aggregate pairing product equation

    let alpha_g1_r_sum = pvk.vk.alpha_g1.mul(r_sum);
    source1.push(alpha_g1_r_sum.into_affine());
    source2.push(pvk.vk.beta_g2);

    let inp = aggregate_public_inputs(public_inputs, &r_powers, r_sum, &pvk.vk.gamma_abc_g1);
    let d_r = VariableBaseMSM::multi_scalar_mul(
        &d,
        &(cfg_iter!(r_powers)
            .map(|r| r.into_repr())
            .collect::<Vec<_>>()),
    );

    source1.push(d_r.add_mixed(&inp).into_affine());
    source2.push(pvk.vk.gamma_g2);

    source1.push(proof.z_c);
    source2.push(pvk.vk.delta_g2);

    checker.add_sources_and_target(&source1, &source2, &proof.z_ab, false);

    match checker.verify() {
        true => Ok(()),
        false => Err(AggregationError::InvalidProof(
            "Proof Verification Failed due to pairing checks".to_string(),
        )),
    }
}
