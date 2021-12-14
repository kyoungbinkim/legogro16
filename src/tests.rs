use crate::{create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof};
use ark_ec::{AffineCurve, PairingEngine, ProjectiveCurve};
use ark_ff::{PrimeField, UniformRand};
use ark_std::rand::{rngs::StdRng, SeedableRng};

use core::ops::MulAssign;

use crate::prover::verify_commitment;
use crate::verifier::get_commitment_to_witnesses;
use ark_ff::Field;
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

fn test_prove_and_verify<E>(n_iters: usize)
where
    E: PairingEngine,
{
    let mut rng = StdRng::seed_from_u64(0u64);

    let num_instance_variables = 2; // There is 1 public input and there is always an instance variable as 1

    // Commit to both witnesses `a` and `b` in the proof
    {
        let commit_witness_count = 2;

        // Generators for committing to instance variables and witnesses and 1 more for randomness (`link_v` below)
        let pedersen_bases = (0..num_instance_variables + commit_witness_count + 1)
            .map(|_| E::G1Projective::rand(&mut rng).into_affine())
            .collect::<Vec<_>>();

        let circuit = MySillyCircuit { a: None, b: None };

        let params = generate_random_parameters::<E, _, _>(
            circuit,
            pedersen_bases.clone(),
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
            assert!(verify_commitment(&params.vk, &proof, &[c], &[a, b], &v, &link_v).unwrap());
            assert!(!verify_commitment(&params.vk, &proof, &[c], &[a], &v, &link_v).unwrap());
            assert!(!verify_commitment(&params.vk, &proof, &[a], &[a, b], &v, &link_v).unwrap());

            assert!(verify_proof(&pvk, &proof).unwrap());

            assert_eq!(
                get_commitment_to_witnesses(&params.vk, &proof, &[c]).unwrap(),
                (pedersen_bases[2].mul(a.into_repr())
                    + pedersen_bases[3].mul(b.into_repr())
                    + pedersen_bases[4].mul(link_v.into_repr()))
                .into_affine()
            );
        }
    }

    // Commit to only 1 witness `a` in the proof
    {
        let commit_witness_count = 1;

        // Generators for committing to instance variables and witnesses and 1 more for randomness (`link_v` below)
        let pedersen_bases = (0..num_instance_variables + commit_witness_count + 1)
            .map(|_| E::G1Projective::rand(&mut rng).into_affine())
            .collect::<Vec<_>>();

        let circuit = MySillyCircuit { a: None, b: None };

        let params = generate_random_parameters::<E, _, _>(
            circuit,
            pedersen_bases.clone(),
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
            assert!(verify_commitment(&params.vk, &proof, &[c], &[a], &v, &link_v).unwrap());
            assert!(!verify_commitment(&params.vk, &proof, &[c], &[a, b], &v, &link_v).unwrap());
            assert!(!verify_commitment(&params.vk, &proof, &[b], &[a], &v, &link_v).unwrap());

            assert!(verify_proof(&pvk, &proof).unwrap());

            assert_eq!(
                get_commitment_to_witnesses(&params.vk, &proof, &[c]).unwrap(),
                (pedersen_bases[2].mul(a.into_repr()) + pedersen_bases[3].mul(link_v.into_repr()))
                    .into_affine()
            );
        }
    }
}

fn test_prove_and_verify_1<E>(n_iters: usize)
where
    E: PairingEngine,
{
    let mut rng = StdRng::seed_from_u64(0u64);

    let num_instance_variables = 2; // There is 1 public input and there is always an instance variable as 1

    // Commit to all 4 witnesses `a`, `b`, `c` and `d` in the proof
    let commit_witness_count = 4;

    // Generators for committing to instance variables and witnesses and 1 more for randomness (`link_v` below)
    let pedersen_bases = (0..num_instance_variables + commit_witness_count + 1)
        .map(|_| E::G1Projective::rand(&mut rng).into_affine())
        .collect::<Vec<_>>();

    let params = generate_random_parameters::<E, _, _>(
        MyLessSillyCircuit {
            a: None,
            b: None,
            c: None,
            d: None,
        },
        pedersen_bases.clone(),
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
        assert!(verify_commitment(&params.vk, &proof, &[y], &[a, b, c, d], &v, &link_v).unwrap());
        assert!(!verify_commitment(&params.vk, &proof, &[a], &[a, b, c, d], &v, &link_v).unwrap());
        assert!(!verify_commitment(&params.vk, &proof, &[y], &[a, b, c], &v, &link_v).unwrap());

        assert!(verify_proof(&pvk, &proof).unwrap());

        assert_eq!(
            get_commitment_to_witnesses(&params.vk, &proof, &[y]).unwrap(),
            (pedersen_bases[2].mul(a.into_repr())
                + pedersen_bases[3].mul(b.into_repr())
                + pedersen_bases[4].mul(c.into_repr())
                + pedersen_bases[5].mul(d.into_repr())
                + pedersen_bases[6].mul(link_v.into_repr()))
            .into_affine()
        );
    }
}

fn test_prove_and_verify_2<E>(n_iters: usize)
where
    E: PairingEngine,
{
    let mut rng = StdRng::seed_from_u64(0u64);

    let num_instance_variables = 3; // There are 2 public inputs and there is always an instance variable as 1

    // Commit to all 4 witnesses `a`, `b`, `c` and `d` in the proof
    let commit_witness_count = 4;

    // Generators for committing to instance variables and witnesses and 1 more for randomness (`link_v` below)
    let pedersen_bases = (0..num_instance_variables + commit_witness_count + 1)
        .map(|_| E::G1Projective::rand(&mut rng).into_affine())
        .collect::<Vec<_>>();

    let params = generate_random_parameters::<E, _, _>(
        MyLessSillyCircuit1 {
            a: None,
            b: None,
            c: None,
            d: None,
        },
        pedersen_bases.clone(),
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
        assert!(
            verify_commitment(&params.vk, &proof, &[e, f], &[a, b, c, d], &v, &link_v).unwrap()
        );
        assert!(
            !verify_commitment(&params.vk, &proof, &[a, b], &[a, b, c, d], &v, &link_v).unwrap()
        );
        assert!(!verify_commitment(&params.vk, &proof, &[e, f], &[a, b], &v, &link_v).unwrap());

        assert!(verify_proof(&pvk, &proof).unwrap());

        assert_eq!(
            get_commitment_to_witnesses(&params.vk, &proof, &[e, f]).unwrap(),
            (pedersen_bases[3].mul(a.into_repr())
                + pedersen_bases[4].mul(b.into_repr())
                + pedersen_bases[5].mul(c.into_repr())
                + pedersen_bases[6].mul(d.into_repr())
                + pedersen_bases[7].mul(link_v.into_repr()))
            .into_affine()
        );
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
