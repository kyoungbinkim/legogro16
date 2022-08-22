use crate::circom::error::CircomError;
use crate::circom::r1cs::R1CS;
use ark_ec::PairingEngine;
use ark_relations::r1cs::{
    ConstraintSynthesizer, ConstraintSystemRef, LinearCombination, SynthesisError, Variable,
};
use ark_std::vec::Vec;

#[derive(Clone, Debug)]
pub struct CircomCircuit<E: PairingEngine> {
    pub r1cs: R1CS<E>,
    /// All wires of the circuit, including the public and private input wires as well as the intermediate wires.
    /// The 1st is always "1", followed by public input wires followed by the private (witness) wires.
    pub wires: Option<Vec<E::Fr>>,
}

impl<E: PairingEngine> CircomCircuit<E> {
    pub fn setup(r1cs: R1CS<E>) -> Self {
        Self { r1cs, wires: None }
    }

    #[cfg(feature = "std")]
    pub fn from_r1cs_file(path: impl AsRef<std::path::Path>) -> Result<Self, CircomError> {
        use crate::circom::r1cs::R1CSFile;
        let r1cs_file = R1CSFile::<E>::new_from_file(path).map_err(|err| {
            log::error!("Encountered error while opening R1CS file: {:?}", err);
            CircomError::UnableToOpenR1CSFile(format!(
                "Encountered error while opening R1CS file: {:?}",
                err
            ))
        })?;
        let r1cs = R1CS::from(r1cs_file);
        Ok(Self::setup(r1cs))
    }
}

impl<'a, E: PairingEngine> CircomCircuit<E> {
    pub fn get_public_inputs(&self) -> Option<Vec<E::Fr>> {
        match &self.wires {
            None => None,
            Some(w) => Some(w[1..self.r1cs.num_public].to_vec()),
        }
    }
}

impl<E: PairingEngine> ConstraintSynthesizer<E::Fr> for CircomCircuit<E> {
    fn generate_constraints(self, cs: ConstraintSystemRef<E::Fr>) -> Result<(), SynthesisError> {
        let wires = &self.wires;

        let dummy = E::Fr::from(0u32);

        // Start from 1 because Arkworks implicitly allocates One for the first input
        for i in 1..self.r1cs.num_public {
            cs.new_input_variable(|| {
                Ok(match wires {
                    None => dummy,
                    Some(w) => w[i],
                })
            })?;
        }

        for i in 0..self.r1cs.num_aux {
            cs.new_witness_variable(|| {
                Ok(match wires {
                    None => dummy,
                    Some(w) => w[i + self.r1cs.num_public],
                })
            })?;
        }

        let make_index = |index| {
            if index < self.r1cs.num_public {
                Variable::Instance(index)
            } else {
                Variable::Witness(index - self.r1cs.num_public)
            }
        };
        let make_lc = |lc_data: &[(usize, E::Fr)]| {
            lc_data.iter().fold(
                LinearCombination::<E::Fr>::zero(),
                |lc: LinearCombination<E::Fr>, (index, coeff)| lc + (*coeff, make_index(*index)),
            )
        };

        for constraint in &self.r1cs.constraints {
            cs.enforce_constraint(
                make_lc(&constraint.0),
                make_lc(&constraint.1),
                make_lc(&constraint.2),
            )?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::circom::tests::{abs_path, gen_params};
    use ark_bls12_381::Bls12_381;
    use ark_bn254::Bn254;
    use ark_relations::r1cs::ConstraintSystem;

    fn generate_params_and_circuit<E: PairingEngine>(
        r1cs_file_path: &str,
        commit_witness_count: usize,
        inputs: Vec<E::Fr>,
    ) {
        let mut circuit = CircomCircuit::<E>::from_r1cs_file(abs_path(r1cs_file_path)).unwrap();

        let cs = ConstraintSystem::<E::Fr>::new_ref();
        circuit.clone().generate_constraints(cs.clone()).unwrap();

        gen_params::<E>(commit_witness_count, circuit.clone());

        circuit.wires = Some(inputs);
        let cs = ConstraintSystem::<E::Fr>::new_ref();
        circuit.clone().generate_constraints(cs.clone()).unwrap();
        assert!(cs.is_satisfied().unwrap());
    }

    #[test]
    fn multiply2_bn128() {
        let r1cs_file_path = "test-vectors/bn128/multiply2.r1cs";
        let wits = vec![1, 33, 3, 11]
            .into_iter()
            .map(|w| <Bn254 as PairingEngine>::Fr::from(w))
            .collect::<Vec<_>>();
        generate_params_and_circuit::<Bn254>(r1cs_file_path, 1, wits.clone());
        generate_params_and_circuit::<Bn254>(r1cs_file_path, 2, wits);
    }

    #[test]
    fn multiply2_bls12_381() {
        let r1cs_file_path = "test-vectors/bls12-381/multiply2.r1cs";
        let wits = vec![1, 33, 3, 11]
            .into_iter()
            .map(|w| <Bls12_381 as PairingEngine>::Fr::from(w))
            .collect::<Vec<_>>();
        generate_params_and_circuit::<Bls12_381>(r1cs_file_path, 1, wits.clone());
        generate_params_and_circuit::<Bls12_381>(r1cs_file_path, 2, wits);
    }

    #[test]
    fn test_1_bn128() {
        let r1cs_file_path = "test-vectors/bn128/test1.r1cs";
        let wits = vec![1, 35, 3, 9]
            .into_iter()
            .map(|w| <Bn254 as PairingEngine>::Fr::from(w))
            .collect::<Vec<_>>();
        generate_params_and_circuit::<Bn254>(r1cs_file_path, 1, wits);
    }

    #[test]
    fn test_1_bls12_381() {
        let r1cs_file_path = "test-vectors/bls12-381/test1.r1cs";
        let wits = vec![1, 35, 3, 9]
            .into_iter()
            .map(|w| <Bls12_381 as PairingEngine>::Fr::from(w))
            .collect::<Vec<_>>();
        generate_params_and_circuit::<Bls12_381>(r1cs_file_path, 1, wits);
    }

    #[test]
    fn test_2_bn128() {
        let r1cs_file_path = "test-vectors/bn128/test2.r1cs";
        let wits = vec![1, 12, 1, 2, 1, 4]
            .into_iter()
            .map(|w| <Bn254 as PairingEngine>::Fr::from(w))
            .collect::<Vec<_>>();
        generate_params_and_circuit::<Bn254>(r1cs_file_path, 1, wits.clone());
        generate_params_and_circuit::<Bn254>(r1cs_file_path, 2, wits);
    }

    #[test]
    fn test_2_bls12_381() {
        let r1cs_file_path = "test-vectors/bls12-381/test2.r1cs";
        let wits = vec![1, 12, 1, 2, 1, 4]
            .into_iter()
            .map(|w| <Bls12_381 as PairingEngine>::Fr::from(w))
            .collect::<Vec<_>>();
        generate_params_and_circuit::<Bls12_381>(r1cs_file_path, 1, wits.clone());
        generate_params_and_circuit::<Bls12_381>(r1cs_file_path, 2, wits);
    }
}
