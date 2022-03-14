use crate::{
    create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof,
    LinkPublicGenerators,
};
use ark_ec::{PairingEngine, ProjectiveCurve};
use ark_ff::Field;
use ark_std::{
    rand::{rngs::StdRng, RngCore, SeedableRng},
    UniformRand,
};

use core::ops::MulAssign;

use crate::prover::verify_commitment;
use ark_relations::r1cs::Variable;
use ark_relations::{
    lc,
    r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError},
};

/// Circuit for computation a * b
#[derive(Clone)]
struct MySillyCircuit<F: Field> {
    a: Option<F>,
    b: Option<F>,
}

/// Circuit for computation a * b + c * d
#[derive(Clone)]
struct MyLessSillyCircuit<F: Field> {
    a: Option<F>,
    b: Option<F>,
    c: Option<F>,
    d: Option<F>,
}

/// Circuit with 2 public inputs, 1st should be equal to a * b and 2nd to c * d
#[derive(Clone)]
struct MyLessSillyCircuit1<F: Field> {
    a: Option<F>,
    b: Option<F>,
    c: Option<F>,
    d: Option<F>,
}

// NOTE: It is necessary to allocate the witness variables that need to be committed before any other
// variable is allocated. This can however be a limitation when a commitment to some indirect witnesses
// (ones that are computed in the circuit) is needed.

impl<ConstraintF: Field> ConstraintSynthesizer<ConstraintF> for MySillyCircuit<ConstraintF> {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<ConstraintF>,
    ) -> Result<(), SynthesisError> {
        let a = cs.new_witness_variable(|| self.a.ok_or(SynthesisError::AssignmentMissing))?;
        let b = cs.new_witness_variable(|| self.b.ok_or(SynthesisError::AssignmentMissing))?;
        let c = cs.new_input_variable(|| {
            let mut a = self.a.ok_or(SynthesisError::AssignmentMissing)?;
            let b = self.b.ok_or(SynthesisError::AssignmentMissing)?;

            a.mul_assign(&b);
            Ok(a)
        })?;

        cs.enforce_constraint(lc!() + a, lc!() + b, lc!() + c)?;
        Ok(())
    }
}

impl<ConstraintF: Field> ConstraintSynthesizer<ConstraintF> for MyLessSillyCircuit<ConstraintF> {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<ConstraintF>,
    ) -> Result<(), SynthesisError> {
        let a = cs.new_witness_variable(|| self.a.ok_or(SynthesisError::AssignmentMissing))?;
        let b = cs.new_witness_variable(|| self.b.ok_or(SynthesisError::AssignmentMissing))?;
        let c = cs.new_witness_variable(|| self.c.ok_or(SynthesisError::AssignmentMissing))?;
        let d = cs.new_witness_variable(|| self.d.ok_or(SynthesisError::AssignmentMissing))?;

        // a * b
        let e_value = if self.a.is_some() && self.b.is_some() {
            Some(self.a.unwrap().mul(self.b.unwrap()))
        } else {
            None
        };
        let e = cs.new_witness_variable(|| e_value.ok_or(SynthesisError::AssignmentMissing))?;
        cs.enforce_constraint(lc!() + a, lc!() + b, lc!() + e)?;

        // c * d
        let f_value = if self.c.is_some() && self.d.is_some() {
            Some(self.c.unwrap().mul(self.d.unwrap()))
        } else {
            None
        };
        let f = cs.new_witness_variable(|| f_value.ok_or(SynthesisError::AssignmentMissing))?;
        cs.enforce_constraint(lc!() + c, lc!() + d, lc!() + f)?;

        let y = cs.new_input_variable(|| {
            let e = e_value.ok_or(SynthesisError::AssignmentMissing)?;
            let f = f_value.ok_or(SynthesisError::AssignmentMissing)?;

            Ok(e + f)
        })?;

        cs.enforce_constraint(lc!() + e + f, lc!() + Variable::One, lc!() + y)?;

        Ok(())
    }
}

impl<ConstraintF: Field> ConstraintSynthesizer<ConstraintF> for MyLessSillyCircuit1<ConstraintF> {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<ConstraintF>,
    ) -> Result<(), SynthesisError> {
        let a = cs.new_witness_variable(|| self.a.ok_or(SynthesisError::AssignmentMissing))?;
        let b = cs.new_witness_variable(|| self.b.ok_or(SynthesisError::AssignmentMissing))?;
        let c = cs.new_witness_variable(|| self.c.ok_or(SynthesisError::AssignmentMissing))?;
        let d = cs.new_witness_variable(|| self.d.ok_or(SynthesisError::AssignmentMissing))?;

        let e = cs.new_input_variable(|| Ok(self.a.unwrap().mul(self.b.unwrap())))?;
        cs.enforce_constraint(lc!() + a, lc!() + b, lc!() + e)?;

        let f = cs.new_input_variable(|| Ok(self.c.unwrap().mul(self.d.unwrap())))?;
        cs.enforce_constraint(lc!() + c, lc!() + d, lc!() + f)?;

        Ok(())
    }
}

pub fn get_link_public_gens<R: RngCore, E: PairingEngine>(
    rng: &mut R,
    count: usize,
) -> LinkPublicGenerators<E> {
    let pedersen_gens = (0..count)
        .map(|_| E::G1Projective::rand(rng).into_affine())
        .collect::<Vec<_>>();
    let g1 = E::G1Projective::rand(rng).into_affine();
    let g2 = E::G2Projective::rand(rng).into_affine();
    LinkPublicGenerators {
        pedersen_gens,
        g1,
        g2,
    }
}

fn test_prove_and_verify<E>(n_iters: usize)
where
    E: PairingEngine,
{
    let mut rng = StdRng::seed_from_u64(0u64);

    // Commit to both witnesses `a` and `b` in the proof
    {
        let commit_witness_count = 2;

        // Generators for committing to witnesses and 1 more for randomness (`link_v` below)
        let link_gens = get_link_public_gens(&mut rng, commit_witness_count + 1);
        let circuit = MySillyCircuit { a: None, b: None };

        let params = generate_random_parameters::<E, _, _>(
            circuit,
            link_gens.clone(),
            commit_witness_count,
            &mut rng,
        )
        .unwrap();

        let pvk = prepare_verifying_key::<E>(&params.vk);

        for _ in 0..n_iters {
            let a = E::Fr::rand(&mut rng);
            let b = E::Fr::rand(&mut rng);
            // let a = E::Fr::from(2u64);
            // let b = E::Fr::from(3u64);
            let mut c = a;
            c.mul_assign(&b);

            // Create commitment randomness
            let v = E::Fr::rand(&mut rng);
            let link_v = E::Fr::rand(&mut rng);

            let circuit = MySillyCircuit {
                a: Some(a),
                b: Some(b),
            };

            // Create a LegoGro16 proof with our parameters.
            let proof = create_random_proof(circuit, v, link_v, &params, &mut rng).unwrap();

            // Prover verifies the openings of the commitments
            verify_commitment(&params.vk, &proof, 1, &[a, b], &v, &link_v).unwrap();
            assert!(verify_commitment(&params.vk, &proof, 1, &[a], &v, &link_v).is_err());
            assert!(verify_commitment(&params.vk, &proof, 2, &[a, b], &v, &link_v).is_err());

            verify_proof(&pvk, &proof, &[c]).unwrap();
        }
    }

    // Commit to only 1 witness `a` in the proof
    {
        let commit_witness_count = 1;

        // Generators for committing to witnesses and 1 more for randomness (`link_v` below)
        let link_gens = get_link_public_gens(&mut rng, commit_witness_count + 1);

        let circuit = MySillyCircuit { a: None, b: None };

        let params = generate_random_parameters::<E, _, _>(
            circuit,
            link_gens.clone(),
            commit_witness_count,
            &mut rng,
        )
        .unwrap();

        let pvk = prepare_verifying_key::<E>(&params.vk);

        for _ in 0..n_iters {
            let a = E::Fr::rand(&mut rng);
            let b = E::Fr::rand(&mut rng);
            // let a = E::Fr::from(2u64);
            // let b = E::Fr::from(3u64);
            let mut c = a;
            c.mul_assign(&b);

            // Create commitment randomness
            let v = E::Fr::rand(&mut rng);
            let link_v = E::Fr::rand(&mut rng);

            let circuit = MySillyCircuit {
                a: Some(a),
                b: Some(b),
            };

            // Create a LegoGro16 proof with our parameters.
            let proof = create_random_proof(circuit, v, link_v, &params, &mut rng).unwrap();

            // Prover verifies the openings of the commitments
            verify_commitment(&params.vk, &proof, 1, &[a], &v, &link_v).unwrap();
            assert!(verify_commitment(&params.vk, &proof, 1, &[a, b], &v, &link_v).is_err());
            assert!(verify_commitment(&params.vk, &proof, 2, &[a], &v, &link_v).is_err());

            verify_proof(&pvk, &proof, &[c]).unwrap();
        }
    }
}

fn test_prove_and_verify_1<E>(n_iters: usize)
where
    E: PairingEngine,
{
    let mut rng = StdRng::seed_from_u64(0u64);

    // Commit to all 4 witnesses `a`, `b`, `c` and `d` in the proof
    let commit_witness_count = 4;

    // Generators for committing to witnesses and 1 more for randomness (`link_v` below)
    let link_gens = get_link_public_gens(&mut rng, commit_witness_count + 1);

    let params = generate_random_parameters::<E, _, _>(
        MyLessSillyCircuit {
            a: None,
            b: None,
            c: None,
            d: None,
        },
        link_gens.clone(),
        commit_witness_count,
        &mut rng,
    )
    .unwrap();

    let pvk = prepare_verifying_key::<E>(&params.vk);

    for _ in 0..n_iters {
        let a = E::Fr::rand(&mut rng);
        let b = E::Fr::rand(&mut rng);
        let c = E::Fr::rand(&mut rng);
        let d = E::Fr::rand(&mut rng);
        // let a = E::Fr::from(2u64);
        // let b = E::Fr::from(3u64);
        // let c = E::Fr::from(4u64);
        // let d = E::Fr::from(5u64);

        let e = a * b;

        let f = c * d;

        let y = e + f;

        // Create commitment randomness
        let v = E::Fr::rand(&mut rng);
        let link_v = E::Fr::rand(&mut rng);

        // Create a LegoGro16 proof with our parameters.
        let circuit = MyLessSillyCircuit {
            a: Some(a),
            b: Some(b),
            c: Some(c),
            d: Some(d),
        };

        let proof = create_random_proof(circuit, v, link_v, &params, &mut rng).unwrap();

        // Prover verifies the openings of the commitments
        verify_commitment(&params.vk, &proof, 1, &[a, b, c, d], &v, &link_v).unwrap();
        assert!(verify_commitment(&params.vk, &proof, 0, &[a, b, c, d], &v, &link_v).is_err());
        assert!(verify_commitment(&params.vk, &proof, 1, &[a, b, c], &v, &link_v).is_err());

        verify_proof(&pvk, &proof, &[y]).unwrap();
    }
}

fn test_prove_and_verify_2<E>(n_iters: usize)
where
    E: PairingEngine,
{
    let mut rng = StdRng::seed_from_u64(0u64);

    // Commit to all 4 witnesses `a`, `b`, `c` and `d` in the proof
    let commit_witness_count = 4;

    // Generators for committing to witnesses and 1 more for randomness (`link_v` below)
    let link_gens = get_link_public_gens(&mut rng, commit_witness_count + 1);

    let params = generate_random_parameters::<E, _, _>(
        MyLessSillyCircuit1 {
            a: None,
            b: None,
            c: None,
            d: None,
        },
        link_gens.clone(),
        4,
        &mut rng,
    )
    .unwrap();

    let pvk = prepare_verifying_key::<E>(&params.vk);

    for _ in 0..n_iters {
        let a = E::Fr::rand(&mut rng);
        let b = E::Fr::rand(&mut rng);
        let c = E::Fr::rand(&mut rng);
        let d = E::Fr::rand(&mut rng);
        // let a = E::Fr::from(2 as u64);
        // let b = E::Fr::from(3 as u64);
        // let c = E::Fr::from(4 as u64);
        // let d = E::Fr::from(5 as u64);

        let mut e = a;
        e.mul_assign(&b);

        let mut f = c;
        f.mul_assign(&d);

        // Create commitment randomness
        let v = E::Fr::rand(&mut rng);
        let link_v = E::Fr::rand(&mut rng);

        // Create a LegoGro16 proof with our parameters.
        let circuit = MyLessSillyCircuit1 {
            a: Some(a),
            b: Some(b),
            c: Some(c),
            d: Some(d),
        };

        let proof = create_random_proof(circuit, v, link_v, &params, &mut rng).unwrap();
        // Prover verifies the openings of the commitments
        verify_commitment(&params.vk, &proof, 2, &[a, b, c, d], &v, &link_v).unwrap();
        assert!(verify_commitment(&params.vk, &proof, 1, &[a, b, c, d], &v, &link_v).is_err());
        assert!(verify_commitment(&params.vk, &proof, 2, &[a, b], &v, &link_v).is_err());

        verify_proof(&pvk, &proof, &[e, f]).unwrap();
    }
}

mod bls12_377 {
    use super::*;
    use ark_bls12_377::Bls12_377;

    #[test]
    fn prove_and_verify() {
        test_prove_and_verify::<Bls12_377>(10);
    }

    #[test]
    fn prove_and_verify_1() {
        test_prove_and_verify_1::<Bls12_377>(10);
    }

    #[test]
    fn prove_and_verify_2() {
        test_prove_and_verify_2::<Bls12_377>(10);
    }
}

mod cp6_782 {
    use super::*;

    use ark_cp6_782::CP6_782;

    #[test]
    fn prove_and_verify() {
        test_prove_and_verify::<CP6_782>(1);
    }

    #[test]
    fn prove_and_verify_1() {
        test_prove_and_verify_1::<CP6_782>(1);
    }

    #[test]
    fn prove_and_verify_2() {
        test_prove_and_verify_2::<CP6_782>(1);
    }
}
