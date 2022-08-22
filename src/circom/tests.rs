use crate::circom::circuit::CircomCircuit;
use crate::circom::witness::WitnessCalculator;
use crate::tests::get_link_public_gens;
use crate::{
    create_random_proof, generate_random_parameters, generate_random_parameters_incl_cp_link,
    prepare_verifying_key, verify_proof, verify_witness_commitment, ProvingKey, ProvingKeyWithLink,
};
use ark_bls12_381::Bls12_381;
use ark_bn254::Bn254;
use ark_ec::PairingEngine;
use ark_ff::Field;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem};
use ark_std::rand::prelude::StdRng;
use ark_std::rand::SeedableRng;
use ark_std::UniformRand;
use std::collections::HashMap;
use std::ops::AddAssign;
use std::path::PathBuf;

pub fn abs_path(p: &str) -> String {
    let mut path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    path.push(p);
    path.to_string_lossy().to_string()
}

pub fn gen_params<E: PairingEngine>(
    commit_witness_count: usize,
    circuit: CircomCircuit<E>,
) -> (ProvingKeyWithLink<E>, ProvingKey<E>) {
    let mut rng = StdRng::seed_from_u64(0u64);
    let link_gens = get_link_public_gens(&mut rng, commit_witness_count + 1);
    let params_link = generate_random_parameters_incl_cp_link::<E, _, _>(
        circuit.clone(),
        link_gens.clone(),
        commit_witness_count,
        &mut rng,
    )
    .unwrap();
    // Parameters for generating proof without CP_link
    let params =
        generate_random_parameters::<E, _, _>(circuit, commit_witness_count, &mut rng).unwrap();
    (params_link, params)
}

pub fn generate_params_prove_and_verify<
    E: PairingEngine,
    I: IntoIterator<Item = (String, Vec<E::Fr>)>,
>(
    r1cs_file_path: &str,
    wasm_file_path: &str,
    commit_witness_count: usize,
    inputs: I,
) -> Vec<E::Fr> {
    let mut circuit = CircomCircuit::<E>::from_r1cs_file(abs_path(r1cs_file_path)).unwrap();

    let cs = ConstraintSystem::<E::Fr>::new_ref();
    circuit.clone().generate_constraints(cs.clone()).unwrap();
    println!("Constraints generated");

    let (_, params) = gen_params::<E>(commit_witness_count, circuit.clone());
    println!("Params generated");

    let mut wits_calc = WitnessCalculator::<E>::from_wasm_file(wasm_file_path).unwrap();
    let all_inputs = wits_calc.calculate_witnesses::<I>(inputs, false).unwrap();

    circuit.wires = Some(all_inputs);
    let cs = ConstraintSystem::<E::Fr>::new_ref();
    circuit.clone().generate_constraints(cs.clone()).unwrap();
    assert!(cs.is_satisfied().unwrap());

    let public_inputs = circuit.get_public_inputs().unwrap();
    let committed_witnesses = circuit
        .wires
        .clone()
        .unwrap()
        .into_iter()
        .skip(1 + public_inputs.len())
        .take(commit_witness_count)
        .collect::<Vec<_>>();
    // Randomness for the committed witness in proof.d
    let mut rng = StdRng::seed_from_u64(0u64);
    let v = E::Fr::rand(&mut rng);
    let proof = create_random_proof(circuit, v, &params, &mut rng).unwrap();
    println!("Proof generated");

    let pvk = prepare_verifying_key::<E>(&params.vk);
    // Prover verifies the openings of the commitments in proof.d
    verify_witness_commitment(
        &params.vk,
        &proof,
        public_inputs.len(),
        &committed_witnesses,
        &v,
    )
    .unwrap();
    verify_proof(&pvk, &proof, &public_inputs).unwrap();
    println!("Proof verified");
    return public_inputs;
}

fn test3<E: PairingEngine>(r1cs_file_path: &str, wasm_file_path: &str) {
    let mut rng = StdRng::seed_from_u64(100u64);
    let x = E::Fr::rand(&mut rng);
    let y = E::Fr::rand(&mut rng);
    let a = E::Fr::rand(&mut rng);
    let b = E::Fr::rand(&mut rng);
    let c = E::Fr::rand(&mut rng);
    let d = E::Fr::rand(&mut rng);

    let mut inputs = HashMap::new();
    inputs.insert("x".to_string(), vec![x]);
    inputs.insert("y".to_string(), vec![y]);
    inputs.insert("a".to_string(), vec![a]);
    inputs.insert("b".to_string(), vec![b]);
    inputs.insert("c".to_string(), vec![c]);
    inputs.insert("d".to_string(), vec![d]);

    let public = generate_params_prove_and_verify::<E, _>(
        r1cs_file_path,
        wasm_file_path,
        4,
        inputs.clone().into_iter(),
    );

    assert_eq!(public.len(), 4);
    let expected_z1 = a * x + b * y + c * d;
    assert_eq!(expected_z1, public[0]);
    let expected_z2 = c * x + d * y;
    assert_eq!(expected_z2, public[1]);
    assert_eq!(x, public[2]);
    assert_eq!(y, public[3]);
}

fn test4<E: PairingEngine>(r1cs_file_path: &str, wasm_file_path: &str) {
    let mut rng = StdRng::seed_from_u64(100u64);
    let x = E::Fr::rand(&mut rng);
    let y = E::Fr::rand(&mut rng);
    let p = E::Fr::rand(&mut rng);
    let q = E::Fr::rand(&mut rng);
    let a = E::Fr::rand(&mut rng);
    let b = E::Fr::rand(&mut rng);
    let r = E::Fr::rand(&mut rng);
    let s = E::Fr::rand(&mut rng);

    let mut inputs = HashMap::new();
    inputs.insert("x".to_string(), vec![x]);
    inputs.insert("y".to_string(), vec![y]);
    inputs.insert("p".to_string(), vec![p]);
    inputs.insert("q".to_string(), vec![q]);
    inputs.insert("a".to_string(), vec![a]);
    inputs.insert("b".to_string(), vec![b]);
    inputs.insert("r".to_string(), vec![r]);
    inputs.insert("s".to_string(), vec![s]);
    let public = generate_params_prove_and_verify::<E, _>(
        r1cs_file_path,
        wasm_file_path,
        4,
        inputs.clone().into_iter(),
    );

    assert_eq!(public.len(), 6);

    let expected_z1 = a * x + b * y + E::Fr::from(10u64) * p * q
        - E::Fr::from(19u64) * r.square() * r * p
        + E::Fr::from(55u64) * s.square().square() * q.square() * q
        - E::Fr::from(3u64) * x.square()
        + E::Fr::from(6u64) * x * y
        - E::Fr::from(13u64) * y.square() * y
        - r * s * x
        + E::Fr::from(5u64) * a * b * y
        - E::Fr::from(32u64) * a * x * y
        - E::Fr::from(2u64) * x * y * p * q
        - E::Fr::from(100u64);
    assert_eq!(expected_z1, public[0]);

    let expected_z2 = a.square() * a * y + E::Fr::from(3u64) * b.square() * x
        - E::Fr::from(20u64) * x.square() * y.square()
        + E::Fr::from(45u64);
    assert_eq!(expected_z2, public[1]);

    assert_eq!(a, public[2]);
    assert_eq!(b, public[3]);
    assert_eq!(r, public[4]);
    assert_eq!(s, public[5]);
}

fn nconstraints<E: PairingEngine>(
    r1cs_file_path: &str,
    wasm_file_path: &str,
    input: E::Fr,
    commit_witness_count: usize,
    num_constraints: u64,
) {
    let mut inputs = HashMap::new();
    inputs.insert("in".to_string(), vec![input.clone()]);
    let public = generate_params_prove_and_verify::<E, _>(
        r1cs_file_path,
        wasm_file_path,
        commit_witness_count,
        inputs.into_iter(),
    );
    let mut accum = input;
    for i in 1..num_constraints {
        // accum = accum * accum + i;
        accum.square_in_place();
        accum.add_assign(E::Fr::from(i));
    }
    assert_eq!(public[0], accum);
}

fn multiply_n<E: PairingEngine>(
    r1cs_file_path: &str,
    wasm_file_path: &str,
    commit_witness_count: usize,
    input_arr_size: usize,
) {
    let mut rng = StdRng::seed_from_u64(100u64);
    let mut inputs = HashMap::new();
    let inp = (0..input_arr_size)
        .map(|_| E::Fr::rand(&mut rng))
        .collect::<Vec<_>>();
    inputs.insert("in".to_string(), inp.clone());
    let public = generate_params_prove_and_verify::<E, _>(
        r1cs_file_path,
        wasm_file_path,
        commit_witness_count,
        inputs.into_iter(),
    );
    let mut expected = E::Fr::from(1u64);
    for i in inp {
        expected *= i;
    }
    assert_eq!(public[0], expected);
}

fn multiply_2_bounded<E: PairingEngine>(
    r1cs_file_path: &str,
    wasm_file_path: &str,
    commit_witness_count: usize,
) {
    let mut rng = StdRng::seed_from_u64(100u64);
    let mut inputs = HashMap::new();
    let mut a = u64::rand(&mut rng);
    while a == 0 {
        a = u64::rand(&mut rng);
    }
    let mut b = u64::rand(&mut rng);
    while b == 0 {
        b = u64::rand(&mut rng);
    }
    inputs.insert("a".to_string(), vec![E::Fr::from(a)]);
    inputs.insert("b".to_string(), vec![E::Fr::from(b)]);
    let public = generate_params_prove_and_verify::<E, _>(
        r1cs_file_path,
        wasm_file_path,
        commit_witness_count,
        inputs.into_iter(),
    );
    assert_eq!(public[0], E::Fr::from(a as u128 * b as u128));
}

fn mimc<E: PairingEngine>(
    r1cs_file_path: &str,
    wasm_file_path: &str,
    commit_witness_count: usize,
    input_arr_size: usize,
) {
    let mut rng = StdRng::seed_from_u64(100u64);
    let mut inputs = HashMap::new();
    let inp = (0..input_arr_size)
        .map(|_| E::Fr::rand(&mut rng))
        .collect::<Vec<_>>();
    inputs.insert("in".to_string(), inp.clone());
    inputs.insert("k".to_string(), vec![E::Fr::from(0u64)]);
    let public = generate_params_prove_and_verify::<E, _>(
        r1cs_file_path,
        wasm_file_path,
        commit_witness_count,
        inputs.into_iter(),
    );
    assert_eq!(public.len(), 1);
}

fn mimcsponge<E: PairingEngine>(
    r1cs_file_path: &str,
    wasm_file_path: &str,
    commit_witness_count: usize,
    input_arr_size: usize,
    output_arr_size: usize,
) {
    let mut rng = StdRng::seed_from_u64(100u64);
    let mut inputs = HashMap::new();
    let inp = (0..input_arr_size)
        .map(|_| E::Fr::rand(&mut rng))
        .collect::<Vec<_>>();
    inputs.insert("in".to_string(), inp.clone());
    inputs.insert("k".to_string(), vec![E::Fr::from(0u64)]);
    let public = generate_params_prove_and_verify::<E, _>(
        r1cs_file_path,
        wasm_file_path,
        commit_witness_count,
        inputs.into_iter(),
    );
    assert_eq!(public.len(), output_arr_size);
}

fn poseidon<E: PairingEngine>(
    r1cs_file_path: &str,
    wasm_file_path: &str,
    commit_witness_count: usize,
    input_arr_size: usize,
) {
    let mut rng = StdRng::seed_from_u64(100u64);
    let mut inputs = HashMap::new();
    let inp = (0..input_arr_size)
        .map(|_| E::Fr::rand(&mut rng))
        .collect::<Vec<_>>();
    inputs.insert("in".to_string(), inp.clone());
    let public = generate_params_prove_and_verify::<E, _>(
        r1cs_file_path,
        wasm_file_path,
        commit_witness_count,
        inputs.into_iter(),
    );
    assert_eq!(public.len(), 1);
}

#[test]
fn test_3_bn128() {
    let r1cs_file_path = "test-vectors/bn128/test3.r1cs";
    let wasm_file_path = "test-vectors/bn128/test3.wasm";
    test3::<Bn254>(r1cs_file_path, wasm_file_path)
}

#[test]
fn test_3_bls12_381() {
    let r1cs_file_path = "test-vectors/bls12-381/test3.r1cs";
    let wasm_file_path = "test-vectors/bls12-381/test3.wasm";
    test3::<Bls12_381>(r1cs_file_path, wasm_file_path)
}

#[test]
fn test_4_bn128() {
    let r1cs_file_path = "test-vectors/bn128/test4.r1cs";
    let wasm_file_path = "test-vectors/bn128/test4.wasm";
    test4::<Bn254>(r1cs_file_path, wasm_file_path)
}

#[test]
fn test_4_bls12_381() {
    let r1cs_file_path = "test-vectors/bls12-381/test4.r1cs";
    let wasm_file_path = "test-vectors/bls12-381/test4.wasm";
    test4::<Bls12_381>(r1cs_file_path, wasm_file_path)
}

#[test]
fn nconstraints_bn128() {
    let r1cs_file_path = "test-vectors/bn128/nconstraints.r1cs";
    let wasm_file_path = "test-vectors/bn128/nconstraints.wasm";
    let num_constraints = 2500;
    let mut rng = StdRng::seed_from_u64(100u64);
    nconstraints::<Bn254>(
        r1cs_file_path,
        wasm_file_path,
        <Bn254 as PairingEngine>::Fr::rand(&mut rng),
        1,
        num_constraints,
    );
}

#[test]
fn nconstraints_bls12_381() {
    let r1cs_file_path = "test-vectors/bls12-381/nconstraints.r1cs";
    let wasm_file_path = "test-vectors/bls12-381/nconstraints.wasm";
    let num_constraints = 2500;
    let mut rng = StdRng::seed_from_u64(100u64);
    nconstraints::<Bls12_381>(
        r1cs_file_path,
        wasm_file_path,
        <Bls12_381 as PairingEngine>::Fr::rand(&mut rng),
        1,
        num_constraints,
    );
}

#[test]
fn multiply_n_bn128() {
    let r1cs_file_path = "test-vectors/bn128/multiply_n.r1cs";
    let wasm_file_path = "test-vectors/bn128/multiply_n.wasm";
    let input_arr_size = 300;
    multiply_n::<Bn254>(
        r1cs_file_path,
        wasm_file_path,
        input_arr_size,
        input_arr_size,
    );
}

#[test]
fn multiply_n_bls12_381() {
    let r1cs_file_path = "test-vectors/bls12-381/multiply_n.r1cs";
    let wasm_file_path = "test-vectors/bls12-381/multiply_n.wasm";
    let input_arr_size = 300;
    multiply_n::<Bls12_381>(
        r1cs_file_path,
        wasm_file_path,
        input_arr_size,
        input_arr_size,
    );
}

#[test]
fn multiply2_bounded_bn128() {
    let r1cs_file_path = "test-vectors/bn128/multiply2_bounded.r1cs";
    let wasm_file_path = "test-vectors/bn128/multiply2_bounded.wasm";
    multiply_2_bounded::<Bn254>(r1cs_file_path, wasm_file_path, 2);
}

#[test]
fn multiply2_bounded_bls12_381() {
    let r1cs_file_path = "test-vectors/bls12-381/multiply2_bounded.r1cs";
    let wasm_file_path = "test-vectors/bls12-381/multiply2_bounded.wasm";
    multiply_2_bounded::<Bls12_381>(r1cs_file_path, wasm_file_path, 2);
}

#[test]
fn mimc_bn128() {
    let r1cs_file_path = "test-vectors/bn128/mimc_bn128.r1cs";
    let wasm_file_path = "test-vectors/bn128/mimc_bn128.wasm";
    mimc::<Bn254>(r1cs_file_path, wasm_file_path, 8, 8);
}

#[test]
fn mimc_bls12_381() {
    let r1cs_file_path = "test-vectors/bls12-381/mimc_bls12_381.r1cs";
    let wasm_file_path = "test-vectors/bls12-381/mimc_bls12_381.wasm";
    mimc::<Bls12_381>(r1cs_file_path, wasm_file_path, 8, 8);
}

#[test]
fn mimcsponge_bn128() {
    let r1cs_file_path = "test-vectors/bn128/mimcsponge_bn128.r1cs";
    let wasm_file_path = "test-vectors/bn128/mimcsponge_bn128.wasm";
    mimcsponge::<Bn254>(r1cs_file_path, wasm_file_path, 8, 2, 3);
}

#[test]
fn mimcsponge_bls12_381() {
    let r1cs_file_path = "test-vectors/bls12-381/mimcsponge_bls12_381.r1cs";
    let wasm_file_path = "test-vectors/bls12-381/mimcsponge_bls12_381.wasm";
    mimcsponge::<Bls12_381>(r1cs_file_path, wasm_file_path, 8, 2, 3);
}

#[ignore]
#[test]
fn poseidon_bn128() {
    let r1cs_file_path = "test-vectors/bn128/poseidon_bn128.r1cs";
    let wasm_file_path = "test-vectors/bn128/poseidon_bn128.wasm";
    poseidon::<Bn254>(r1cs_file_path, wasm_file_path, 5, 5);
}
