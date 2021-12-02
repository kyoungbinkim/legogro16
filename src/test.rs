use crate::{
    create_random_proof, generate_random_parameters, prepare_verifying_key, verify_commitment,
    verify_proof,
};
use ark_ec::{PairingEngine, ProjectiveCurve};
use ark_ff::{PrimeField, UniformRand};
use ark_std::rand::{rngs::StdRng, SeedableRng};

use core::ops::MulAssign;
use ark_ec::group::Group;

use ark_ff::{Field, Zero};
use ark_relations::{
    lc,
    r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError},
};
use ark_relations::r1cs::{ConstraintSystem, LcIndex, Variable, ConstraintLayer, TracingMode};
use tracing_subscriber::layer::SubscriberExt;

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

#[derive(Clone)]
struct MyLessSillyCircuit1<F: Field> {
    a: Option<F>,
    b: Option<F>,
    c: Option<F>,
    d: Option<F>,
}

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
        // cs.enforce_constraint(lc!() + a, lc!() + b, lc!() + c)?;
        // cs.enforce_constraint(lc!() + a, lc!() + b, lc!() + c)?;
        // cs.enforce_constraint(lc!() + a, lc!() + b, lc!() + c)?;
        // cs.enforce_constraint(lc!() + a, lc!() + b, lc!() + c)?;
        // cs.enforce_constraint(lc!() + a, lc!() + b, lc!() + c)?;

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
        } else {None};
        let e =
            cs.new_witness_variable(|| e_value.ok_or(SynthesisError::AssignmentMissing))?;
        cs.enforce_constraint(
            lc!() + a,
            lc!() + b,
            lc!() + e,
        )?;

        // c * d
        let f_value = if self.c.is_some() && self.d.is_some() {
            Some(self.c.unwrap().mul(self.d.unwrap()))
        } else {None};
        let f =
            cs.new_witness_variable(|| f_value.ok_or(SynthesisError::AssignmentMissing))?;
        cs.enforce_constraint(
            lc!() + c,
            lc!() + d,
            lc!() + f,
        )?;

        let y = cs.new_input_variable(|| {
            let e = e_value.ok_or(SynthesisError::AssignmentMissing)?;
            let f = f_value.ok_or(SynthesisError::AssignmentMissing)?;

            Ok(e + f)
        })?;

        cs.enforce_constraint(
            lc!() + e + f,
            lc!() + Variable::One,
            lc!() + y,
        )?;

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

        let e = cs.new_input_variable(|| {
            Ok(self.a.unwrap().mul(self.b.unwrap()))
        })?;
        cs.enforce_constraint(
            lc!() + a,
            lc!() + b,
            lc!() + e,
        )?;

        let f = cs.new_input_variable(|| {
            Ok(self.c.unwrap().mul(self.d.unwrap()))
        })?;
        cs.enforce_constraint(
            lc!() + c,
            lc!() + d,
            lc!() + f,
        )?;

        Ok(())
    }
}

fn test_prove_and_verify<E>(n_iters: usize)
where
    E: PairingEngine,
{
    let mut rng = StdRng::seed_from_u64(0u64);

    let pedersen_bases = (0..3)
        .map(|_| E::G1Projective::rand(&mut rng).into_affine())
        .collect::<Vec<_>>();

    let params = generate_random_parameters::<E, _, _>(
        MySillyCircuit { a: None, b: None },
        &pedersen_bases,
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

        // Question: What if there are more than 2 instance variables?
        // Create commitment randomness
        let v = E::Fr::rand(&mut rng);
        let link_v = E::Fr::rand(&mut rng);

        let circuit = MySillyCircuit {
            a: Some(a),
            b: Some(b),
        };

        // let cs = ConstraintSystem::new_ref();
        // circuit.clone().generate_constraints(cs.clone()).unwrap();
        // println!("{:?}", cs.which_is_unsatisfied());
        // println!("{:?}", cs.to_matrices());

        // Create a LegoGro16 proof with our parameters.
        let proof = create_random_proof(
            circuit,
            v,
            link_v,
            &params,
            &mut rng,
        )
        .unwrap();

        assert!(verify_proof(&pvk, &proof).unwrap());
        assert!(verify_commitment(&pvk, &proof, &[c], &v, &link_v).unwrap());
        assert!(!verify_commitment(&pvk, &proof, &[a], &v, &link_v).unwrap());
        assert!(!verify_commitment(&pvk, &proof, &[c], &a, &link_v).unwrap());
    }
}

fn test_prove_and_verify_1<E>(n_iters: usize)
    where
        E: PairingEngine,
{
    let mut rng = StdRng::seed_from_u64(0u64);

    let pedersen_bases = (0..3)
        .map(|_| E::G1Projective::rand(&mut rng).into_affine())
        .collect::<Vec<_>>();

    let params = generate_random_parameters::<E, _, _>(
        MyLessSillyCircuit { a: None, b: None, c: None, d: None },
        &pedersen_bases,
        &mut rng,
    )
        .unwrap();

    let pvk = prepare_verifying_key::<E>(&params.vk);

    for _ in 0..n_iters {
        // let a = E::Fr::rand(&mut rng);
        // let b = E::Fr::rand(&mut rng);
        // let c = E::Fr::rand(&mut rng);
        // let d = E::Fr::rand(&mut rng);
        let a = E::Fr::from(2u64);
        let b = E::Fr::from(3u64);
        let c = E::Fr::from(4u64);
        let d = E::Fr::from(5u64);

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

        // First, some boilerplat that helps with debugging
        let mut layer = ConstraintLayer::default();
        layer.mode = TracingMode::All;
        let subscriber = tracing_subscriber::Registry::default().with(layer);
        let _guard = tracing::subscriber::set_default(subscriber);

        // let cs = ConstraintSystem::new_ref();
        // circuit.clone().generate_constraints(cs.clone()).unwrap();
        // println!("{:?}", cs.which_is_unsatisfied());
        // println!("{:?}", cs.assigned_value(Variable::Instance(0)).unwrap().into_repr());
        // println!("{:?}", cs.assigned_value(Variable::Instance(1)).unwrap().into_repr());
        // println!("{:?}", cs.assigned_value(Variable::Witness(0)).unwrap().into_repr());
        // println!("{:?}", cs.assigned_value(Variable::Witness(1)).unwrap().into_repr());
        // println!("{:?}", cs.assigned_value(Variable::Witness(2)).unwrap().into_repr());
        // println!("{:?}", cs.assigned_value(Variable::Witness(3)).unwrap().into_repr());
        // println!("{:?}", cs.assigned_value(Variable::Witness(4)).unwrap().into_repr());
        // println!("{:?}", cs.assigned_value(Variable::Witness(5)).unwrap().into_repr());
        // println!("{:?}", cs.constraint_names());
        // println!("{:?}", cs.to_matrices());

        let proof = create_random_proof(
            circuit,
            v,
            link_v,
            &params,
            &mut rng,
        )
            .unwrap();

        assert!(verify_proof(&pvk, &proof).unwrap());
        assert!(verify_commitment(&pvk, &proof, &[y], &v, &link_v).unwrap());
        assert!(!verify_commitment(&pvk, &proof, &[a], &v, &link_v).unwrap());
        assert!(!verify_commitment(&pvk, &proof, &[c], &a, &link_v).unwrap());
    }
}

fn test_prove_and_verify_2<E>(n_iters: usize)
    where
        E: PairingEngine,
{
    let mut rng = StdRng::seed_from_u64(0u64);

    let pedersen_bases = (0..4)
        .map(|_| E::G1Projective::rand(&mut rng).into_affine())
        .collect::<Vec<_>>();

    let params = generate_random_parameters::<E, _, _>(
        MyLessSillyCircuit1 { a: None, b: None, c: None, d: None },
        &pedersen_bases,
        &mut rng,
    )
        .unwrap();

    let pvk = prepare_verifying_key::<E>(&params.vk);

    for _ in 0..n_iters {
        // let a = E::Fr::rand(&mut rng);
        // let b = E::Fr::rand(&mut rng);
        // let c = E::Fr::rand(&mut rng);
        // let d = E::Fr::rand(&mut rng);
        let a = E::Fr::from(2 as u64);
        let b = E::Fr::from(3 as u64);
        let c = E::Fr::from(4 as u64);
        let d = E::Fr::from(5 as u64);

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

        let proof = create_random_proof(
            circuit,
            v,
            link_v,
            &params,
            &mut rng,
        )
            .unwrap();

        assert!(verify_proof(&pvk, &proof).unwrap());
        assert!(verify_commitment(&pvk, &proof, &[e, f], &v, &link_v).unwrap());
        assert!(!verify_commitment(&pvk, &proof, &[a, b], &v, &link_v).unwrap());
        assert!(!verify_commitment(&pvk, &proof, &[c, d], &v, &link_v).unwrap());
    }
}

mod bls12_377 {
    use super::*;
    use ark_bls12_377::Bls12_377;

    #[test]
    fn prove_and_verify() {
        test_prove_and_verify::<Bls12_377>(100);
    }

    #[test]
    fn prove_and_verify_1() {
        test_prove_and_verify_1::<Bls12_377>(1);
    }

    #[test]
    fn prove_and_verify_2() {
        test_prove_and_verify_2::<Bls12_377>(1);
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
}
