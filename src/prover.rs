use crate::{
    link::{PESubspaceSnark, SubspaceSnark},
    r1cs_to_qap::LibsnarkReduction,
    Proof, ProofWithLink, ProvingKey, ProvingKeyCommon, ProvingKeyWithLink, VerifyingKey,
    VerifyingKeyWithLink,
};
use ark_ec::{msm::VariableBaseMSM, AffineCurve, PairingEngine, ProjectiveCurve};
use ark_ff::{PrimeField, UniformRand, Zero};
use ark_poly::GeneralEvaluationDomain;
use ark_relations::r1cs::{
    ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, OptimizationGoal,
};
use ark_std::rand::Rng;
use ark_std::{cfg_into_iter, cfg_iter, end_timer, start_timer, vec, vec::Vec};

use crate::error::Error;
use crate::r1cs_to_qap::R1CStoQAP;
use ark_std::ops::AddAssign;
#[cfg(feature = "parallel")]
use rayon::prelude::*;

/// Create a LegoGroth16 proof that is zero-knowledge.
/// This method samples randomness for zero knowledge via `rng`.
#[inline]
pub fn create_random_proof_incl_cp_link<E, C, R>(
    circuit: C,
    v: E::Fr,
    link_v: E::Fr,
    pk: &ProvingKeyWithLink<E>,
    rng: &mut R,
) -> crate::Result<ProofWithLink<E>>
where
    E: PairingEngine,
    C: ConstraintSynthesizer<E::Fr>,
    R: Rng,
{
    let r = E::Fr::rand(rng);
    let s = E::Fr::rand(rng);

    create_proof_incl_cp_link::<E, C>(circuit, pk, r, s, v, link_v)
}

/// Create a LegoGroth16 proof that is zero-knowledge.
/// This method samples randomness for zero knowledge via `rng`.
#[inline]
pub fn create_random_proof<E, C, R>(
    circuit: C,
    v: E::Fr,
    pk: &ProvingKey<E>,
    rng: &mut R,
) -> crate::Result<Proof<E>>
where
    E: PairingEngine,
    C: ConstraintSynthesizer<E::Fr>,
    R: Rng,
{
    let r = E::Fr::rand(rng);
    let s = E::Fr::rand(rng);

    create_proof::<E, C>(circuit, pk, r, s, v)
}

#[inline]
/// Create a LegoGroth16 proof using randomness `r` and `s`.
pub fn create_proof_incl_cp_link<E, C>(
    circuit: C,
    pk: &ProvingKeyWithLink<E>,
    r: E::Fr,
    s: E::Fr,
    v: E::Fr,
    link_v: E::Fr,
) -> crate::Result<ProofWithLink<E>>
where
    E: PairingEngine,
    C: ConstraintSynthesizer<E::Fr>,
{
    create_proof_incl_cp_link_with_reduction::<E, C, LibsnarkReduction>(
        circuit, pk, r, s, v, link_v,
    )
}

#[inline]
/// Create a LegoGroth16 proof using randomness `r` and `s`.
pub fn create_proof<E, C>(
    circuit: C,
    pk: &ProvingKey<E>,
    r: E::Fr,
    s: E::Fr,
    v: E::Fr,
) -> crate::Result<Proof<E>>
where
    E: PairingEngine,
    C: ConstraintSynthesizer<E::Fr>,
{
    create_proof_with_reduction::<E, C, LibsnarkReduction>(circuit, pk, r, s, v)
}

/// Create a LegoGroth16 proof using randomness `r` and `s`.
/// `v` is the randomness of the commitment `proof.d` and `link_v` is the randomness to cp_link commitment
#[inline]
pub fn create_proof_incl_cp_link_with_reduction<E, C, QAP>(
    circuit: C,
    pk: &ProvingKeyWithLink<E>,
    r: E::Fr,
    s: E::Fr,
    v: E::Fr,
    link_v: E::Fr,
) -> crate::Result<ProofWithLink<E>>
where
    E: PairingEngine,
    C: ConstraintSynthesizer<E::Fr>,
    QAP: R1CStoQAP,
{
    let prover_time = start_timer!(|| "Groth16::Prover");
    let (cs, h) = synthesize_circuit::<E, C, QAP>(circuit)?;

    let prover = cs.borrow().unwrap();
    let proof = create_proof_incl_cp_link_with_assignment::<E, QAP>(
        pk,
        r,
        s,
        v,
        link_v,
        &h,
        &prover.instance_assignment,
        &prover.witness_assignment,
    )?;

    drop(prover);
    drop(cs);

    end_timer!(prover_time);

    Ok(proof)
}

/// Create a LegoGroth16 proof using randomness `r` and `s`.
/// `v` is the randomness of the commitment `proof.d` and `link_v` is the randomness to cp_link commitment
#[inline]
pub fn create_proof_with_reduction<E, C, QAP>(
    circuit: C,
    pk: &ProvingKey<E>,
    r: E::Fr,
    s: E::Fr,
    v: E::Fr,
) -> crate::Result<Proof<E>>
where
    E: PairingEngine,
    C: ConstraintSynthesizer<E::Fr>,
    QAP: R1CStoQAP,
{
    let prover_time = start_timer!(|| "Groth16::Prover");
    let (cs, h) = synthesize_circuit::<E, C, QAP>(circuit)?;

    let prover = cs.borrow().unwrap();
    let proof = create_proof_with_assignment::<E, QAP>(
        pk,
        r,
        s,
        v,
        &h,
        &prover.instance_assignment,
        &prover.witness_assignment,
    )?;

    drop(prover);
    drop(cs);

    end_timer!(prover_time);

    Ok(proof)
}

#[inline]
fn create_proof_incl_cp_link_with_assignment<E, QAP>(
    pk: &ProvingKeyWithLink<E>,
    r: E::Fr,
    s: E::Fr,
    v: E::Fr,
    link_v: E::Fr,
    h: &[E::Fr],
    input_assignment: &[E::Fr],
    witness_assignment: &[E::Fr],
) -> crate::Result<ProofWithLink<E>>
where
    E: PairingEngine,
    QAP: R1CStoQAP,
{
    let (proof, comm_wits) = create_proof_and_committed_witnesses_with_assignment::<E, QAP>(
        &pk.common,
        &pk.vk.groth16_vk,
        r,
        s,
        v,
        &h,
        input_assignment,
        witness_assignment,
    )?;

    let mut comm_wits_with_link_hider = cfg_iter!(comm_wits)
        .map(|w| w.into_repr())
        .collect::<Vec<_>>();
    comm_wits_with_link_hider.push(link_v.into_repr());

    let g_d_link = VariableBaseMSM::multi_scalar_mul(&pk.vk.link_bases, &comm_wits_with_link_hider);

    let mut ss_snark_witness = comm_wits;
    ss_snark_witness.push(link_v);
    ss_snark_witness.push(v);

    let link_time = start_timer!(|| "Compute CP_{link}");
    let link_pi = PESubspaceSnark::<E>::prove(&pk.vk.link_pp, &pk.link_ek, &ss_snark_witness)?;

    end_timer!(link_time);

    drop(comm_wits_with_link_hider);
    drop(ss_snark_witness);

    Ok(ProofWithLink {
        groth16_proof: proof,
        link_d: g_d_link.into_affine(),
        link_pi,
    })
}

#[inline]
fn create_proof_with_assignment<E, QAP>(
    pk: &ProvingKey<E>,
    r: E::Fr,
    s: E::Fr,
    v: E::Fr,
    h: &[E::Fr],
    input_assignment: &[E::Fr],
    witness_assignment: &[E::Fr],
) -> crate::Result<Proof<E>>
where
    E: PairingEngine,
    QAP: R1CStoQAP,
{
    let (proof, _comm_wits) = create_proof_and_committed_witnesses_with_assignment::<E, QAP>(
        &pk.common,
        &pk.vk,
        r,
        s,
        v,
        &h,
        input_assignment,
        witness_assignment,
    )?;
    drop(_comm_wits);
    Ok(proof)
}

#[inline]
fn create_proof_and_committed_witnesses_with_assignment<E, QAP>(
    pk_common: &ProvingKeyCommon<E>,
    vk: &VerifyingKey<E>,
    r: E::Fr,
    s: E::Fr,
    v: E::Fr,
    h: &[E::Fr],
    input_assignment: &[E::Fr],
    witness_assignment: &[E::Fr],
) -> crate::Result<(Proof<E>, Vec<E::Fr>)>
where
    E: PairingEngine,
    QAP: R1CStoQAP,
{
    let h_assignment = cfg_into_iter!(h).map(|s| s.into_repr()).collect::<Vec<_>>();
    let c_acc_time = start_timer!(|| "Compute C");

    let h_acc = VariableBaseMSM::multi_scalar_mul(&pk_common.h_query, &h_assignment);
    drop(h_assignment);

    let v_repr = v.into_repr();

    // Compute C
    let aux_assignment = cfg_iter!(witness_assignment)
        .map(|s| s.into_repr())
        .collect::<Vec<_>>();

    let committed_witnesses = &aux_assignment[..pk_common.commit_witness_count];
    let uncommitted_witnesses = &aux_assignment[pk_common.commit_witness_count..];

    let l_aux_acc = VariableBaseMSM::multi_scalar_mul(&pk_common.l_query, uncommitted_witnesses);

    let v_eta_delta_inv = pk_common.eta_delta_inv_g1.into_projective().mul(v_repr);

    end_timer!(c_acc_time);

    let r_repr = r.into_repr();
    let s_repr = s.into_repr();
    let rs_repr = (r * s).into_repr();
    let delta_g1_proj = pk_common.delta_g1.into_projective();

    let input_assignment_wth_one = cfg_iter!(input_assignment)
        .map(|s| s.into_repr())
        .collect::<Vec<_>>();

    let mut assignment = vec![];
    assignment.extend_from_slice(&input_assignment_wth_one[1..]);
    assignment.extend_from_slice(&aux_assignment);

    // Compute A
    let a_acc_time = start_timer!(|| "Compute A");
    let r_g1 = delta_g1_proj.mul(r_repr);
    let g_a = calculate_coeff(r_g1, &pk_common.a_query, vk.alpha_g1, &assignment);
    end_timer!(a_acc_time);

    // Compute B in G1 if needed
    let g1_b = if !r.is_zero() {
        let b_g1_acc_time = start_timer!(|| "Compute B in G1");
        let s_g1 = delta_g1_proj.mul(s_repr);
        let g1_b = calculate_coeff(s_g1, &pk_common.b_g1_query, pk_common.beta_g1, &assignment);
        end_timer!(b_g1_acc_time);

        g1_b
    } else {
        E::G1Projective::zero()
    };

    // Compute B in G2
    let b_g2_acc_time = start_timer!(|| "Compute B in G2");
    let s_g2 = vk.delta_g2.into_projective().mul(s_repr);
    let g2_b = calculate_coeff(s_g2, &pk_common.b_g2_query, vk.beta_g2, &assignment);
    drop(assignment);

    end_timer!(b_g2_acc_time);

    let c_time = start_timer!(|| "Finish C");
    let mut g_c = g_a.mul(s_repr);
    g_c += &g1_b.mul(r_repr);
    g_c -= &delta_g1_proj.mul(rs_repr);
    g_c += &l_aux_acc;
    g_c += &h_acc;
    g_c -= &v_eta_delta_inv;
    end_timer!(c_time);

    // Compute D
    let d_acc_time = start_timer!(|| "Compute D");

    let gamma_abc_inputs_source = &vk.gamma_abc_g1[input_assignment_wth_one.len()
        ..input_assignment_wth_one.len() + committed_witnesses.len()];
    let gamma_abc_inputs_acc =
        VariableBaseMSM::multi_scalar_mul(gamma_abc_inputs_source, &committed_witnesses);

    let v_eta_gamma_inv = vk.eta_gamma_inv_g1.into_projective().mul(v_repr);

    let mut g_d = gamma_abc_inputs_acc;
    g_d += &v_eta_gamma_inv;
    end_timer!(d_acc_time);

    let committed_witnesses = witness_assignment[..pk_common.commit_witness_count].to_vec();
    drop(aux_assignment);

    Ok((
        Proof {
            a: g_a.into_affine(),
            b: g2_b.into_affine(),
            c: g_c.into_affine(),
            d: g_d.into_affine(),
        },
        committed_witnesses,
    ))
}

/// Check the opening of cp_link.
pub fn verify_link_commitment<E: PairingEngine>(
    cp_link_bases: &[E::G1Affine],
    link_d: &E::G1Affine,
    witnesses_expected_in_commitment: &[E::Fr],
    link_v: &E::Fr,
) -> crate::Result<()> {
    // Some witnesses are committed in `link_d` with randomness `link_v`
    if (witnesses_expected_in_commitment.len() + 1) > cp_link_bases.len() {
        return Err(Error::VectorLongerThanExpected(
            witnesses_expected_in_commitment.len() + 1,
            cp_link_bases.len(),
        ));
    }
    let mut committed = cfg_iter!(witnesses_expected_in_commitment)
        .map(|p| p.into_repr())
        .collect::<Vec<_>>();
    committed.push(link_v.into_repr());

    if *link_d != VariableBaseMSM::multi_scalar_mul(cp_link_bases, &committed).into_affine() {
        return Err(Error::InvalidLinkCommitment);
    }
    Ok(())
}

/// Check that the commitments in the proof open to the public inputs and the witnesses but with different
/// bases and randomness. This function is only called by the prover, the verifier does not
/// know `witnesses_expected_in_commitment` or `link_v`.
pub fn verify_commitments<E: PairingEngine>(
    vk: &VerifyingKeyWithLink<E>,
    proof: &ProofWithLink<E>,
    public_inputs_count: usize,
    witnesses_expected_in_commitment: &[E::Fr],
    v: &E::Fr,
    link_v: &E::Fr,
) -> crate::Result<()> {
    verify_link_commitment::<E>(
        &vk.link_bases,
        &proof.link_d,
        witnesses_expected_in_commitment,
        link_v,
    )?;
    verify_witness_commitment::<E>(
        &vk.groth16_vk,
        &proof.groth16_proof,
        public_inputs_count,
        witnesses_expected_in_commitment,
        v,
    )
}

pub fn verify_witness_commitment<E: PairingEngine>(
    vk: &VerifyingKey<E>,
    proof: &Proof<E>,
    public_inputs_count: usize,
    witnesses_expected_in_commitment: &[E::Fr],
    v: &E::Fr,
) -> crate::Result<()> {
    // Some witnesses are also committed in `proof.d` with randomness `v`
    if (public_inputs_count + witnesses_expected_in_commitment.len() + 1) > vk.gamma_abc_g1.len() {
        return Err(Error::VectorLongerThanExpected(
            public_inputs_count + witnesses_expected_in_commitment.len() + 1,
            vk.gamma_abc_g1.len(),
        ));
    }
    let committed = cfg_iter!(witnesses_expected_in_commitment)
        .map(|p| p.into_repr())
        .collect::<Vec<_>>();

    // Check that proof.d is correctly constructed.
    let mut d = VariableBaseMSM::multi_scalar_mul(
        &vk.gamma_abc_g1[1 + public_inputs_count..1 + public_inputs_count + committed.len()],
        &committed,
    );
    d.add_assign(&vk.eta_gamma_inv_g1.mul(v.into_repr()));

    if proof.d != d.into_affine() {
        return Err(Error::InvalidProofCommitment);
    }

    Ok(())
}

#[inline]
pub fn synthesize_circuit<E, C, QAP>(
    circuit: C,
) -> crate::Result<(ConstraintSystemRef<E::Fr>, Vec<E::Fr>)>
where
    E: PairingEngine,
    C: ConstraintSynthesizer<E::Fr>,
    QAP: R1CStoQAP,
{
    let cs = ConstraintSystem::new_ref();

    // Set the optimization goal
    cs.set_optimization_goal(OptimizationGoal::Constraints);

    // Synthesize the circuit.
    let synthesis_time = start_timer!(|| "Constraint synthesis");
    circuit.generate_constraints(cs.clone())?;
    debug_assert!(cs.is_satisfied().unwrap());
    end_timer!(synthesis_time);

    let lc_time = start_timer!(|| "Inlining LCs");
    cs.finalize();
    end_timer!(lc_time);

    let witness_map_time = start_timer!(|| "R1CS to QAP witness map");
    let h = QAP::witness_map::<E::Fr, GeneralEvaluationDomain<E::Fr>>(cs.clone())?;
    end_timer!(witness_map_time);
    Ok((cs, h))
}

fn calculate_coeff<G: AffineCurve>(
    initial: G::Projective,
    query: &[G],
    vk_param: G,
    assignment: &[<G::ScalarField as PrimeField>::BigInt],
) -> G::Projective {
    let el = query[0];
    let acc = VariableBaseMSM::multi_scalar_mul(&query[1..], assignment);

    let mut res = initial;
    res.add_assign_mixed(&el);
    res += &acc;
    res.add_assign_mixed(&vk_param);

    res
}
