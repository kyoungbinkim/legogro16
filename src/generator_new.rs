use crate::{
    link::{PESubspaceSnark, SparseMatrix, SubspaceSnark, PP},
    r1cs_to_qap::R1CStoQAP,
    ProvingKeyNew, Vec, VerifyingKey,
};
use ark_ec::{msm::FixedBaseMSM, AffineCurve, PairingEngine, ProjectiveCurve};
use ark_ff::{Field, PrimeField, UniformRand, Zero};
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};
use ark_relations::r1cs::{
    ConstraintSynthesizer, ConstraintSystem, OptimizationGoal, Result as R1CSResult,
    SynthesisError, SynthesisMode,
};
use ark_std::rand::Rng;
use ark_std::{cfg_into_iter, cfg_iter, end_timer, start_timer};

#[cfg(feature = "parallel")]
use rayon::prelude::*;

/// Generates a random common reference string for
/// a circuit.
#[inline]
pub fn generate_random_parameters_new<E, C, R>(
    circuit: C,
    pedersen_bases: &[E::G1Affine],
    commit_witness_count: usize,
    rng: &mut R,
) -> R1CSResult<ProvingKeyNew<E>>
where
    E: PairingEngine,
    C: ConstraintSynthesizer<E::Fr>,
    R: Rng,
{
    let alpha = E::Fr::rand(rng);
    let beta = E::Fr::rand(rng);
    let gamma = E::Fr::rand(rng);
    let delta = E::Fr::rand(rng);
    let eta = E::Fr::rand(rng);

    generate_parameters_new::<E, C, R>(
        circuit,
        alpha,
        beta,
        gamma,
        delta,
        eta,
        pedersen_bases,
        commit_witness_count,
        rng,
    )
}

/// Create parameters for a circuit, given some toxic waste.
pub fn generate_parameters_new<E, C, R>(
    circuit: C,
    alpha: E::Fr,
    beta: E::Fr,
    gamma: E::Fr,
    delta: E::Fr,
    eta: E::Fr,
    pedersen_bases: &[E::G1Affine],
    commit_witness_count: usize,
    rng: &mut R,
) -> R1CSResult<ProvingKeyNew<E>>
where
    E: PairingEngine,
    C: ConstraintSynthesizer<E::Fr>,
    R: Rng,
{
    type D<F> = GeneralEvaluationDomain<F>;

    let setup_time = start_timer!(|| "Groth16::Generator");
    let cs = ConstraintSystem::new_ref();
    cs.set_optimization_goal(OptimizationGoal::Constraints);
    cs.set_mode(SynthesisMode::Setup);

    // Synthesize the circuit.
    let synthesis_time = start_timer!(|| "Constraint synthesis");
    circuit.generate_constraints(cs.clone())?;
    end_timer!(synthesis_time);

    let lc_time = start_timer!(|| "Inlining LCs");
    cs.finalize();
    end_timer!(lc_time);

    ///////////////////////////////////////////////////////////////////////////
    let domain_time = start_timer!(|| "Constructing evaluation domain");

    let domain_size = cs.num_constraints() + cs.num_instance_variables();
    let domain = D::new(domain_size).ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
    let t = domain.sample_element_outside_domain(rng);

    end_timer!(domain_time);
    ///////////////////////////////////////////////////////////////////////////

    let num_instance_variables = cs.num_instance_variables();
    assert!(cs.num_witness_variables() >= commit_witness_count);

    let total_to_commit = num_instance_variables + commit_witness_count;

    let reduction_time = start_timer!(|| "R1CS to QAP Instance Map with Evaluation");
    let (a, b, c, zt, qap_num_variables, m_raw) =
        R1CStoQAP::instance_map_with_evaluation::<E::Fr, D<E::Fr>>(cs, &t)?;
    end_timer!(reduction_time);

    // Compute query densities
    let non_zero_a: usize = cfg_into_iter!(0..qap_num_variables)
        .map(|i| usize::from(!a[i].is_zero()))
        .sum();

    let non_zero_b: usize = cfg_into_iter!(0..qap_num_variables)
        .map(|i| usize::from(!b[i].is_zero()))
        .sum();

    let scalar_bits = E::Fr::size_in_bits();

    let gamma_inverse = gamma.inverse().ok_or(SynthesisError::UnexpectedIdentity)?;
    let delta_inverse = delta.inverse().ok_or(SynthesisError::UnexpectedIdentity)?;

    let gamma_abc = cfg_iter!(a[..total_to_commit])
        .zip(&b[..total_to_commit])
        .zip(&c[..total_to_commit])
        .map(|((a, b), c)| (beta * a + &(alpha * b) + c) * &gamma_inverse)
        .collect::<Vec<_>>();

    // println!("abc");
    // println!("a:");
    // for i in a[..num_instance_variables].iter() {
    //     println!("{:?}", i.into_repr());
    // }
    // println!("b:");
    // for i in b[..num_instance_variables].iter() {
    //     println!("{:?}", i.into_repr());
    // }
    // println!("c:");
    // for i in c[..num_instance_variables].iter() {
    //     println!("{:?}", i.into_repr());
    // }

    let l = cfg_iter!(a)
        .zip(&b)
        .zip(&c)
        .map(|((a, b), c)| (beta * a + &(alpha * b) + c) * &delta_inverse)
        .collect::<Vec<_>>();

    drop(c);

    let g1_generator = E::G1Projective::rand(rng);
    let g2_generator = E::G2Projective::rand(rng);

    // Compute B window table
    let g2_time = start_timer!(|| "Compute G2 table");
    let g2_window = FixedBaseMSM::get_mul_window_size(non_zero_b);
    let g2_table =
        FixedBaseMSM::get_window_table::<E::G2Projective>(scalar_bits, g2_window, g2_generator);
    end_timer!(g2_time);

    // Compute the B-query in G2
    let b_g2_time = start_timer!(|| "Calculate B G2");
    let b_g2_query =
        FixedBaseMSM::multi_scalar_mul::<E::G2Projective>(scalar_bits, g2_window, &g2_table, &b);
    drop(g2_table);
    end_timer!(b_g2_time);

    // Compute G window table
    let g1_window_time = start_timer!(|| "Compute G1 window table");
    let g1_window =
        FixedBaseMSM::get_mul_window_size(non_zero_a + non_zero_b + qap_num_variables + m_raw + 1);
    let g1_table =
        FixedBaseMSM::get_window_table::<E::G1Projective>(scalar_bits, g1_window, g1_generator);
    end_timer!(g1_window_time);

    // Generate the R1CS proving key
    let proving_key_time = start_timer!(|| "Generate the R1CS proving key");

    let beta_repr = beta.into_repr();
    let delta_repr = delta.into_repr();

    let alpha_g1 = g1_generator.mul(alpha.into_repr());
    let beta_g1 = g1_generator.mul(beta_repr);
    let beta_g2 = g2_generator.mul(beta_repr);
    let delta_g1 = g1_generator.mul(delta_repr);
    let delta_g2 = g2_generator.mul(delta_repr);

    // Compute the A-query
    let a_time = start_timer!(|| "Calculate A");
    let a_query =
        FixedBaseMSM::multi_scalar_mul::<E::G1Projective>(scalar_bits, g1_window, &g1_table, &a);
    drop(a);
    end_timer!(a_time);

    // Compute the B-query in G1
    let b_g1_time = start_timer!(|| "Calculate B G1");
    let b_g1_query =
        FixedBaseMSM::multi_scalar_mul::<E::G1Projective>(scalar_bits, g1_window, &g1_table, &b);
    drop(b);
    end_timer!(b_g1_time);

    // Compute the H-query
    let h_time = start_timer!(|| "Calculate H");
    let h_query = FixedBaseMSM::multi_scalar_mul::<E::G1Projective>(
        scalar_bits,
        g1_window,
        &g1_table,
        &cfg_into_iter!(0..m_raw - 1)
            .map(|i| zt * &delta_inverse * &t.pow([i as u64]))
            .collect::<Vec<_>>(),
    );

    end_timer!(h_time);

    // Compute the L-query
    let l_time = start_timer!(|| "Calculate L");
    let l_query = FixedBaseMSM::multi_scalar_mul::<E::G1Projective>(
        scalar_bits,
        g1_window,
        &g1_table,
        &l[total_to_commit..],
    );
    drop(l);
    end_timer!(l_time);

    end_timer!(proving_key_time);

    // Generate R1CS verification key
    let verifying_key_time = start_timer!(|| "Generate the R1CS verification key");
    let gamma_g2 = g2_generator.mul(gamma.into_repr());
    let gamma_abc_g1 = FixedBaseMSM::multi_scalar_mul::<E::G1Projective>(
        scalar_bits,
        g1_window,
        &g1_table,
        &gamma_abc,
    );

    drop(g1_table);

    end_timer!(verifying_key_time);

    let eta_gamma_inv_g1 = g1_generator.mul((eta * &gamma_inverse).into_repr());

    let link_rows = 2; // we're comparing two commitments
    let link_cols = gamma_abc_g1.len() + 2; // we have len inputs and 1 hiding factor per row
    let link_pp = PP::<E::G1Affine, E::G2Affine> {
        l: link_rows,
        t: link_cols,
        g1: E::G1Affine::prime_subgroup_generator(),
        g2: E::G2Affine::prime_subgroup_generator(),
    };
    // println!("gamma_abc_g1 len={:?}", gamma_abc_g1.len());

    let mut link_m = SparseMatrix::<E::G1Affine>::new(link_rows, link_cols);
    link_m.insert_row_slice(0, 0, &pedersen_bases);
    link_m.insert_row_slice(
        1,
        0,
        &gamma_abc_g1
            .iter()
            .map(|p| p.into_affine())
            .collect::<Vec<_>>(),
    );
    link_m.insert_row_slice(1, gamma_abc_g1.len() + 1, &[eta_gamma_inv_g1.into_affine()]);

    let (link_ek, link_vk) = PESubspaceSnark::<E>::keygen(rng, &link_pp, link_m);

    let vk = VerifyingKey::<E> {
        alpha_g1: alpha_g1.into_affine(),
        beta_g2: beta_g2.into_affine(),
        gamma_g2: gamma_g2.into_affine(),
        delta_g2: delta_g2.into_affine(),
        gamma_abc_g1: E::G1Projective::batch_normalization_into_affine(&gamma_abc_g1),
        eta_gamma_inv_g1: eta_gamma_inv_g1.into_affine(),

        link_pp,
        link_bases: pedersen_bases.to_vec(),
        link_vk,
    };

    let batch_normalization_time = start_timer!(|| "Convert proving key elements to affine");
    let a_query = E::G1Projective::batch_normalization_into_affine(&a_query);
    let b_g1_query = E::G1Projective::batch_normalization_into_affine(&b_g1_query);
    let b_g2_query = E::G2Projective::batch_normalization_into_affine(&b_g2_query);
    let h_query = E::G1Projective::batch_normalization_into_affine(&h_query);
    let l_query = E::G1Projective::batch_normalization_into_affine(&l_query);
    end_timer!(batch_normalization_time);
    end_timer!(setup_time);

    let eta_delta_inv_g1 = g1_generator.mul((eta * &delta_inverse).into_repr());

    Ok(ProvingKeyNew {
        vk,
        beta_g1: beta_g1.into_affine(),
        delta_g1: delta_g1.into_affine(),
        eta_delta_inv_g1: eta_delta_inv_g1.into_affine(),
        a_query,
        b_g1_query,
        b_g2_query,
        h_query,
        l_query,
        commit_witness_count,
        link_ek,
    })
}