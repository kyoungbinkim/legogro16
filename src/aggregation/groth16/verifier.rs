use ark_ec::{msm::VariableBaseMSM, AffineCurve, PairingEngine};
use ark_ff::{Field, PrimeField};
use ark_std::ops::{AddAssign, MulAssign};
use ark_std::{cfg_iter, format, rand::Rng, vec, vec::Vec, One, Zero};

use ark_groth16::PreparedVerifyingKey;

#[cfg(feature = "parallel")]
use rayon::prelude::*;

use crate::aggregation::pairing_check::PairingCheck;
use crate::aggregation::srs::{VerifierSRS, VerifierSRSProjective};
use crate::aggregation::utils::{final_verification_check, verify_kzg};

use crate::aggregation::commitment::PairCommitment;
use crate::aggregation::error::AggregationError;
use crate::aggregation::kzg::polynomial_evaluation_product_form_from_transcript;
use crate::aggregation::transcript::Transcript;

use super::proof::AggregateProof;

/// Verifies the aggregated proofs thanks to the Groth16 verifying key, the
/// verifier SRS from the aggregation scheme, all the public inputs of the
/// proofs and the aggregated proof.
///
/// WARNING: transcript_include represents everything that should be included in
/// the transcript from outside the boundary of this function. This is especially
/// relevant for ALL public inputs of ALL individual proofs. In the regular case,
/// one should input ALL public inputs from ALL proofs aggregated. However, IF ALL the
/// public inputs are **fixed, and public before the aggregation time**, then there is
/// no need to hash those. The reason we specify this extra assumption is because hashing
/// the public inputs from the decoded form can take quite some time depending on the
/// number of proofs and public inputs (+100ms in our case). In the case of Filecoin, the only
/// non-fixed part of the public inputs are the challenges derived from a seed. Even though this
/// seed comes from a random beacon, we are hashing this as a safety precaution.
pub fn verify_aggregate_proof<E: PairingEngine, R: Rng, T: Transcript>(
    ip_verifier_srs: &VerifierSRS<E>,
    pvk: &PreparedVerifyingKey<E>,
    public_inputs: &[Vec<E::Fr>],
    proof: &AggregateProof<E>,
    mut rng: R,
    mut transcript: &mut T,
    pairing_check: Option<&mut PairingCheck<E>>,
) -> Result<(), AggregationError> {
    proof.parsing_check()?;
    for pub_input in public_inputs {
        if (pub_input.len() + 1) != pvk.vk.gamma_abc_g1.len() {
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

    let mut c = PairingCheck::new_using_rng(&mut rng);
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

    final_verification_check(
        &mut source1,
        &mut source2,
        proof.z_c.clone(),
        &proof.z_ab,
        &r,
        public_inputs,
        &pvk.vk.alpha_g1,
        pvk.vk.beta_g2,
        pvk.vk.gamma_g2,
        pvk.vk.delta_g2,
        &pvk.vk.gamma_abc_g1,
        &mut checker,
    )
}

/// verify_tipp_mipp returns a pairing equation to check the tipp proof.  $r$ is
/// the randomness used to produce a random linear combination of A and B and
/// used in the MIPP part with C
pub fn verify_tipp_mipp<E: PairingEngine, T: Transcript>(
    v_srs: &VerifierSRSProjective<E>,
    proof: &AggregateProof<E>,
    r_shift: &E::Fr,
    transcript: &mut T,
    pairing_checker: &mut PairingCheck<E>,
) -> Result<(), AggregationError> {
    // (T,U), Z for TIPP and MIPP  and all challenges
    let (final_res, final_r, challenges, challenges_inv) =
        gipa_verify_tipp_mipp(&proof, r_shift, transcript);

    // KZG challenge point
    transcript.append(b"kzg-challenge", &challenges[0]);
    transcript.append(b"vkey0", &proof.tmipp.gipa.final_vkey.0);
    transcript.append(b"vkey1", &proof.tmipp.gipa.final_vkey.1);
    transcript.append(b"wkey0", &proof.tmipp.gipa.final_wkey.0);
    transcript.append(b"wkey1", &proof.tmipp.gipa.final_wkey.1);
    let c = transcript.challenge_scalar::<E::Fr>(b"z-challenge");

    verify_kzg(
        v_srs,
        &proof.tmipp.gipa.final_vkey,
        &proof.tmipp.vkey_opening,
        &proof.tmipp.gipa.final_wkey,
        &proof.tmipp.wkey_opening,
        &challenges,
        &challenges_inv,
        &r_shift.inverse().unwrap(),
        &c,
        pairing_checker,
    );

    // We create a sequence of pairing tuple that we aggregate together at
    // the end to perform only once the final exponentiation.

    let b_prep = E::G2Prepared::from(proof.tmipp.gipa.final_b);
    let v_0_prep = E::G2Prepared::from(proof.tmipp.gipa.final_vkey.0);
    let v_1_prep = E::G2Prepared::from(proof.tmipp.gipa.final_vkey.1);

    // TIPP
    // z = e(A,B)
    pairing_checker.add_prepared_sources_and_target(
        &[proof.tmipp.gipa.final_a],
        vec![b_prep.clone()],
        &final_res.zab,
        false,
    );
    //  final_aB.0 = T = e(A,v1)e(w1,B)
    pairing_checker.add_prepared_sources_and_target(
        &[proof.tmipp.gipa.final_a, proof.tmipp.gipa.final_wkey.0],
        vec![v_0_prep.clone(), b_prep.clone()],
        &final_res.tab,
        false,
    );

    //  final_aB.1 = U = e(A,v2)e(w2,B)
    pairing_checker.add_prepared_sources_and_target(
        &[proof.tmipp.gipa.final_a, proof.tmipp.gipa.final_wkey.1],
        vec![v_1_prep.clone(), b_prep],
        &final_res.uab,
        false,
    );

    // MIPP for C
    // Verify base inner product commitment
    // Z ==  c ^ r
    let final_zc = proof.tmipp.gipa.final_c.mul(final_r);
    // Check commitment correctness
    // T = e(C,v1)
    pairing_checker.add_prepared_sources_and_target(
        &[proof.tmipp.gipa.final_c],
        vec![v_0_prep],
        &final_res.tc,
        false,
    );
    // U = e(C,v2)
    pairing_checker.add_prepared_sources_and_target(
        &[proof.tmipp.gipa.final_c],
        vec![v_1_prep],
        &final_res.uc,
        false,
    );

    if final_zc != final_res.zc {
        return Err(AggregationError::InvalidProof(format!(
            "tipp verify: INVALID final_z check for C {} vs {}",
            final_zc, final_res.zc
        )));
    }
    Ok(())
}

/// gipa_verify_tipp_mipp recurse on the proof and statement and produces the final
/// values to be checked by TIPP and MIPP verifier, namely, for TIPP for example:
/// * T,U: the final commitment values of A and B
/// * Z the final product between A and B.
/// * Challenges are returned in inverse order as well to avoid
/// repeating the operation multiple times later on.
/// * There are T,U,Z vectors as well for the MIPP relationship. Both TIPP and
/// MIPP share the same challenges however, enabling to re-use common operations
/// between them, such as the KZG proof for commitment keys.
pub fn gipa_verify_tipp_mipp<E: PairingEngine, T: Transcript>(
    proof: &AggregateProof<E>,
    r_shift: &E::Fr,
    transcript: &mut T,
) -> (GipaTUZ<E>, E::Fr, Vec<E::Fr>, Vec<E::Fr>) {
    let gipa = &proof.tmipp.gipa;
    // COM(A,B) = PROD e(A,B) given by prover
    let comms_ab = &gipa.comms_ab;
    // COM(C,r) = SUM C^r given by prover
    let comms_c = &gipa.comms_c;
    // Z vectors coming from the GIPA proofs
    let zs_ab = &gipa.z_ab;
    let zs_c = &gipa.z_c;

    let mut challenges = Vec::new();
    let mut challenges_inv = Vec::new();

    transcript.append(b"inner-product-ab", &proof.z_ab);
    transcript.append(b"comm-c", &proof.z_c);
    let mut c_inv: E::Fr = transcript.challenge_scalar::<E::Fr>(b"first-challenge");
    let mut c = c_inv.inverse().unwrap();

    // We first generate all challenges as this is the only consecutive process
    // that can not be parallelized then we scale the commitments in a
    // parallelized way
    for (i, ((comm_ab, z_ab), (comm_c, z_c))) in comms_ab
        .iter()
        .zip(zs_ab.iter())
        .zip(comms_c.iter().zip(zs_c.iter()))
        .enumerate()
    {
        let (tab_l, tab_r) = comm_ab;
        let (tuc_l, tuc_r) = comm_c;
        let (zab_l, zab_r) = z_ab;
        let (zc_l, zc_r) = z_c;

        // Fiat-Shamir challenge
        if i == 0 {
            // already generated c_inv and c outside of the loop
        } else {
            transcript.append(b"c_inv", &c_inv);
            transcript.append(b"zab_l", zab_l);
            transcript.append(b"zab_r", zab_r);
            transcript.append(b"zc_l", zc_l);
            transcript.append(b"zc_r", zc_r);
            transcript.append(b"tab_l", tab_l);
            transcript.append(b"tab_r", tab_r);
            transcript.append(b"tuc_l", tuc_l);
            transcript.append(b"tuc_r", tuc_r);
            c_inv = transcript.challenge_scalar::<E::Fr>(b"challenge_i");
            c = c_inv.inverse().unwrap();
        }
        challenges.push(c);
        challenges_inv.push(c_inv);
    }

    // output of the pair commitment T and U in TIPP -> COM((v,w),A,B)
    let PairCommitment { t: t_ab, u: u_ab } = proof.com_ab.clone();
    let z_ab = proof.z_ab; // in the end must be equal to Z = A^r * B

    // COM(v,C)
    let PairCommitment { t: t_c, u: u_c } = proof.com_c.clone();
    let z_c = proof.z_c.into_projective(); // in the end must be equal to Z = C^r

    let mut final_res = GipaTUZ {
        tab: t_ab,
        uab: u_ab,
        zab: z_ab,
        tc: t_c,
        uc: u_c,
        zc: z_c,
    };

    // we first multiply each entry of the Z U and L vectors by the respective
    // challenges independently
    // Since at the end we want to multiple all "t" values together, we do
    // multiply all of them in parallel and then merge then back at the end.
    // same for u and z.
    enum Op<'a, E: PairingEngine> {
        TAB(&'a E::Fqk, <E::Fr as PrimeField>::BigInt),
        UAB(&'a E::Fqk, <E::Fr as PrimeField>::BigInt),
        ZAB(&'a E::Fqk, <E::Fr as PrimeField>::BigInt),
        TC(&'a E::Fqk, <E::Fr as PrimeField>::BigInt),
        UC(&'a E::Fqk, <E::Fr as PrimeField>::BigInt),
    }

    let z_s = cfg_iter!(challenges)
        .zip(cfg_iter!(challenges_inv))
        .flat_map(|(c, c_inv)| [c.into_repr(), c_inv.into_repr()])
        .collect::<Vec<_>>();

    let zc_b = cfg_iter!(zs_c).flat_map(|t| [t.0, t.1]).collect::<Vec<_>>();

    final_res.zc += VariableBaseMSM::multi_scalar_mul(&zc_b, z_s.as_slice());

    let iters = cfg_iter!(comms_ab)
        .zip(cfg_iter!(zs_ab))
        .zip(cfg_iter!(comms_c))
        .zip(cfg_iter!(challenges).zip(cfg_iter!(challenges_inv)))
        .flat_map(|(((comm_ab, z_ab), comm_c), (c, c_inv))| {
            // T and U values for right and left for AB part
            let (PairCommitment { t: tab_l, u: uab_l }, PairCommitment { t: tab_r, u: uab_r }) =
                comm_ab;
            let (zab_l, zab_r) = z_ab;

            // T and U values for right and left for C part
            let (PairCommitment { t: tc_l, u: uc_l }, PairCommitment { t: tc_r, u: uc_r }) = comm_c;

            let c_repr = c.into_repr();
            let c_inv_repr = c_inv.into_repr();

            // we multiple left side by x and right side by x^-1
            vec![
                Op::TAB::<E>(tab_l, c_repr),
                Op::TAB(tab_r, c_inv_repr),
                Op::UAB(uab_l, c_repr),
                Op::UAB(uab_r, c_inv_repr),
                Op::ZAB(zab_l, c_repr),
                Op::ZAB(zab_r, c_inv_repr),
                Op::TC::<E>(tc_l, c_repr),
                Op::TC(tc_r, c_inv_repr),
                Op::UC(uc_l, c_repr),
                Op::UC(uc_r, c_inv_repr),
            ]
        });

    #[cfg(feature = "parallel")]
    let res = iters
        .fold(GipaTUZ::<E>::default, |mut res, op: Op<E>| {
            match op {
                Op::TAB(tx, c) => {
                    let tx: E::Fqk = tx.pow(c);
                    res.tab.mul_assign(&tx);
                }
                Op::UAB(ux, c) => {
                    let ux: E::Fqk = ux.pow(c);
                    res.uab.mul_assign(&ux);
                }
                Op::ZAB(zx, c) => {
                    let zx: E::Fqk = zx.pow(c);
                    res.zab.mul_assign(&zx);
                }

                Op::TC(tx, c) => {
                    let tx: E::Fqk = tx.pow(c);
                    res.tc.mul_assign(&tx);
                }
                Op::UC(ux, c) => {
                    let ux: E::Fqk = ux.pow(c);
                    res.uc.mul_assign(&ux);
                }
            }
            res
        })
        .reduce(GipaTUZ::default, |mut acc_res, res| {
            acc_res.merge(&res);
            acc_res
        });

    #[cfg(not(feature = "parallel"))]
    let res = iters.fold(GipaTUZ::<E>::default(), |mut res, op: Op<E>| {
        match op {
            Op::TAB(tx, c) => {
                let tx: E::Fqk = tx.pow(c);
                res.tab.mul_assign(&tx);
            }
            Op::UAB(ux, c) => {
                let ux: E::Fqk = ux.pow(c);
                res.uab.mul_assign(&ux);
            }
            Op::ZAB(zx, c) => {
                let zx: E::Fqk = zx.pow(c);
                res.zab.mul_assign(&zx);
            }

            Op::TC(tx, c) => {
                let tx: E::Fqk = tx.pow(c);
                res.tc.mul_assign(&tx);
            }
            Op::UC(ux, c) => {
                let ux: E::Fqk = ux.pow(c);
                res.uc.mul_assign(&ux);
            }
        }
        res
    });

    // we reverse the order because the polynomial evaluation routine expects
    // the challenges in reverse order.Doing it here allows us to compute the final_r
    // in log time. Challenges are used as well in the KZG verification checks.
    challenges.reverse();
    challenges_inv.reverse();

    let ref_final_res = &mut final_res;
    let ref_challenges_inv = &challenges_inv;

    ref_final_res.merge(&res);
    let final_r = polynomial_evaluation_product_form_from_transcript(
        ref_challenges_inv,
        r_shift,
        &E::Fr::one(),
    );

    (final_res, final_r, challenges, challenges_inv)
}

/// Keeps track of the variables that have been sent by the prover and must
/// be multiplied together by the verifier. Both MIPP and TIPP are merged
/// together.
pub struct GipaTUZ<E: PairingEngine> {
    pub tab: E::Fqk,
    pub uab: E::Fqk,
    pub zab: E::Fqk,
    pub tc: E::Fqk,
    pub uc: E::Fqk,
    pub zc: E::G1Projective,
}

impl<E> Default for GipaTUZ<E>
where
    E: PairingEngine,
{
    fn default() -> Self {
        Self {
            tab: E::Fqk::one(),
            uab: E::Fqk::one(),
            zab: E::Fqk::one(),
            tc: E::Fqk::one(),
            uc: E::Fqk::one(),
            zc: E::G1Projective::zero(),
        }
    }
}

impl<E> GipaTUZ<E>
where
    E: PairingEngine,
{
    pub fn merge(&mut self, other: &Self) {
        self.tab.mul_assign(&other.tab);
        self.uab.mul_assign(&other.uab);
        self.zab.mul_assign(&other.zab);
        self.tc.mul_assign(&other.tc);
        self.uc.mul_assign(&other.uc);
        self.zc.add_assign(&other.zc);
    }
}
