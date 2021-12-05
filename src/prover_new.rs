use crate::{
    link::{PESubspaceSnark, SubspaceSnark},
    r1cs_to_qap::R1CStoQAP,
    Proof, ProvingKeyNew,
};
use ark_ec::{msm::VariableBaseMSM, AffineCurve, PairingEngine, ProjectiveCurve};
use ark_ff::{PrimeField, UniformRand, Zero};
use ark_poly::GeneralEvaluationDomain;
use ark_relations::r1cs::{
    ConstraintSynthesizer, ConstraintSystem, OptimizationGoal, Result as R1CSResult,
};
use ark_std::rand::Rng;
use ark_std::{cfg_into_iter, cfg_iter, end_timer, start_timer, vec::Vec};

#[cfg(feature = "parallel")]
use rayon::prelude::*;

/// Create a Groth16 proof that is zero-knowledge.
/// This method samples randomness for zero knowledge via `rng`.
#[inline]
pub fn create_random_proof_new<E, C, R>(
    circuit: C,
    v: E::Fr,
    link_v: E::Fr,
    pk: &ProvingKeyNew<E>,
    rng: &mut R,
) -> R1CSResult<Proof<E>>
where
    E: PairingEngine,
    C: ConstraintSynthesizer<E::Fr>,
    R: Rng,
{
    let r = E::Fr::rand(rng);
    let s = E::Fr::rand(rng);

    create_proof_new::<E, C>(circuit, pk, r, s, v, link_v)
}

/// Create a Groth16 proof using randomness `r` and `s`.
#[inline]
pub fn create_proof_new<E, C>(
    circuit: C,
    pk: &ProvingKeyNew<E>,
    r: E::Fr,
    s: E::Fr,
    v: E::Fr,
    link_v: E::Fr,
) -> R1CSResult<Proof<E>>
where
    E: PairingEngine,
    C: ConstraintSynthesizer<E::Fr>,
{
    // TODO: Fix some unnecessary memory allocations
    type D<F> = GeneralEvaluationDomain<F>;

    let prover_time = start_timer!(|| "Groth16::Prover");
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
    let h = R1CStoQAP::witness_map::<E::Fr, D<E::Fr>>(cs.clone())?;
    end_timer!(witness_map_time);
    let h_assignment = cfg_into_iter!(h).map(|s| s.into()).collect::<Vec<_>>();
    let c_acc_time = start_timer!(|| "Compute C");

    let h_acc = VariableBaseMSM::multi_scalar_mul(&pk.h_query, &h_assignment);
    drop(h_assignment);

    let s_repr = s.into_repr();
    let r_repr = r.into_repr();

    // Compute C
    let prover = cs.borrow().unwrap();
    let aux_assignment = cfg_iter!(prover.witness_assignment)
        .map(|s| s.into_repr())
        .collect::<Vec<_>>();

    let committed_witnesses = &aux_assignment[..pk.commit_witness_count];
    let uncommitted_witnesses = &aux_assignment[pk.commit_witness_count..];

    let l_aux_acc = VariableBaseMSM::multi_scalar_mul(&pk.l_query, uncommitted_witnesses);

    let r_s_delta_g1 = pk.delta_g1.into_projective().mul(r_repr).mul(s_repr);
    let v_eta_delta_inv = pk.eta_delta_inv_g1.into_projective().mul(v.into_repr());

    end_timer!(c_acc_time);

    let input_assignment_wth_one = prover
        .instance_assignment
        .iter()
        .map(|s| s.into_repr())
        .collect::<Vec<_>>();

    let mut commit_assignments = input_assignment_wth_one.clone();
    commit_assignments.extend_from_slice(committed_witnesses);

    drop(prover);
    drop(cs);

    let mut assignment = vec![];
    assignment.extend_from_slice(&input_assignment_wth_one[1..]);
    assignment.extend_from_slice(&aux_assignment);
    drop(aux_assignment);

    // Compute A
    let a_acc_time = start_timer!(|| "Compute A");
    let r_g1 = pk.delta_g1.mul(r);

    let g_a = calculate_coeff(r_g1, &pk.a_query, pk.vk.alpha_g1, &assignment);

    let s_g_a = g_a.mul(s_repr);
    end_timer!(a_acc_time);

    // Compute B in G1 if needed
    let g1_b = if !r.is_zero() {
        let b_g1_acc_time = start_timer!(|| "Compute B in G1");
        let s_g1 = pk.delta_g1.mul(s);
        let g1_b = calculate_coeff(s_g1, &pk.b_g1_query, pk.beta_g1, &assignment);

        end_timer!(b_g1_acc_time);

        g1_b
    } else {
        E::G1Projective::zero()
    };

    // Compute B in G2
    let b_g2_acc_time = start_timer!(|| "Compute B in G2");
    let s_g2 = pk.vk.delta_g2.mul(s);
    let g2_b = calculate_coeff(s_g2, &pk.b_g2_query, pk.vk.beta_g2, &assignment);
    let r_g1_b = g1_b.mul(r_repr);
    drop(assignment);

    end_timer!(b_g2_acc_time);

    let c_time = start_timer!(|| "Finish C");
    let mut g_c = s_g_a;
    g_c += &r_g1_b;
    g_c -= &r_s_delta_g1;
    g_c += &l_aux_acc;
    g_c += &h_acc;
    g_c -= &v_eta_delta_inv;
    end_timer!(c_time);

    // Compute D
    let d_acc_time = start_timer!(|| "Compute D");

    let gamma_abc_inputs_source = &pk.vk.gamma_abc_g1;
    let gamma_abc_inputs_acc =
        VariableBaseMSM::multi_scalar_mul(gamma_abc_inputs_source, &commit_assignments);

    let v_eta_gamma_inv = pk.vk.eta_gamma_inv_g1.into_projective().mul(v.into_repr());

    let mut g_d = gamma_abc_inputs_acc;
    g_d += &v_eta_gamma_inv;
    end_timer!(d_acc_time);

    let mut commit_assignments_with_link_hider = vec![];
    commit_assignments_with_link_hider.append(&mut commit_assignments);
    commit_assignments_with_link_hider.push(link_v.into_repr());

    let pedersen_bases_affine = &pk.vk.link_bases;
    let g_d_link = VariableBaseMSM::multi_scalar_mul(
        &pedersen_bases_affine,
        &commit_assignments_with_link_hider,
    );

    let mut ss_snark_witness = commit_assignments_with_link_hider
        .into_iter()
        .map(|b| E::Fr::from_repr(b).unwrap())
        .collect::<Vec<_>>();
    ss_snark_witness.push(v);

    let link_time = start_timer!(|| "Compute CP_{link}");
    let link_pi = PESubspaceSnark::<E>::prove(&pk.vk.link_pp, &pk.link_ek, &ss_snark_witness);

    end_timer!(link_time);

    end_timer!(prover_time);

    Ok(Proof {
        a: g_a.into_affine(),
        b: g2_b.into_affine(),
        c: g_c.into_affine(),
        d: g_d.into_affine(),
        link_d: g_d_link.into_affine(),
        link_pi,
    })
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
