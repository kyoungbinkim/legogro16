use crate::circom::error::CircomError;
use crate::circom::r1cs::{LC, R1CS};
use crate::error::Error;
use crate::{generate_random_parameters, ProvingKey};
use ark_ec::PairingEngine;
use ark_relations::r1cs::{
    ConstraintSynthesizer, ConstraintSystemRef, LinearCombination, SynthesisError, Variable,
};
use ark_std::rand::RngCore;
use ark_std::string::String;
use ark_std::vec::Vec;

use crate::circom::WitnessCalculator;

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
        Ok(Self::setup(r1cs_file.into()))
    }

    pub fn generate_proving_key<R: RngCore>(
        self,
        commit_witness_count: usize,
        rng: &mut R,
    ) -> Result<ProvingKey<E>, Error> {
        generate_random_parameters(self, commit_witness_count, rng)
    }
}

impl<'a, E: PairingEngine> CircomCircuit<E> {
    /// Get the public output and input signals of the circuit excluding the first signal "1".
    /// The returned vector contains the public output signals, followed by the public input signals
    pub fn get_public_inputs(&self) -> Option<Vec<E::Fr>> {
        match &self.wires {
            None => None,
            Some(w) => Some(w[1..self.r1cs.num_public].to_vec()),
        }
    }

    /// Set values for the circuit wires.
    pub fn set_wires(&mut self, wires: Vec<E::Fr>) {
        self.wires = Some(wires);
    }

    pub fn set_wires_using_witness_calculator<I: IntoIterator<Item = (String, Vec<E::Fr>)>>(
        &mut self,
        wit_calc: &mut WitnessCalculator<E>,
        inputs: I,
        sanity_check: bool,
    ) -> Result<(), CircomError> {
        let all_wires = wit_calc.calculate_witnesses::<_>(inputs, sanity_check)?;
        self.wires = Some(all_wires);
        Ok(())
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

        for i in 0..self.r1cs.num_private {
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
        let make_lc = |lc_data: &LC<E>| {
            lc_data.terms().iter().fold(
                LinearCombination::<E::Fr>::zero(),
                |lc: LinearCombination<E::Fr>, (index, coeff)| lc + (*coeff, make_index(*index)),
            )
        };

        for constraint in &self.r1cs.constraints {
            cs.enforce_constraint(
                make_lc(&constraint.a),
                make_lc(&constraint.b),
                make_lc(&constraint.c),
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

    fn generate_params_and_test_circuit<E: PairingEngine>(
        r1cs_file_path: &str,
        commit_witness_count: usize,
        wires: Option<Vec<E::Fr>>,
    ) -> ConstraintSystemRef<E::Fr> {
        let mut circuit = CircomCircuit::<E>::from_r1cs_file(abs_path(r1cs_file_path)).unwrap();

        let cs = ConstraintSystem::<E::Fr>::new_ref();
        circuit.clone().generate_constraints(cs.clone()).unwrap();

        assert_eq!(cs.num_instance_variables(), circuit.r1cs.num_public);
        assert_eq!(cs.num_witness_variables(), circuit.r1cs.num_private);
        assert_eq!(cs.num_constraints(), circuit.r1cs.constraints.len());

        let (_, params) = gen_params::<E>(commit_witness_count, circuit.clone());

        assert_eq!(
            params.vk.gamma_abc_g1.len(),
            cs.num_instance_variables() + commit_witness_count
        );
        assert_eq!(params.vk.num_public_inputs(), circuit.r1cs.num_public);
        assert_eq!(params.vk.num_committed_witnesses(), commit_witness_count);

        if wires.is_some() {
            circuit.set_wires(wires.unwrap());
            let cs = ConstraintSystem::<E::Fr>::new_ref();
            circuit.clone().generate_constraints(cs.clone()).unwrap();
            assert!(cs.is_satisfied().unwrap());
        }

        return cs;
    }

    #[test]
    fn multiply2() {
        fn check<E: PairingEngine>(
            r1cs_file_path: &str,
            commit_witness_count: usize,
            wits: Option<Vec<E::Fr>>,
        ) {
            let cs =
                generate_params_and_test_circuit::<E>(r1cs_file_path, commit_witness_count, wits);
            assert_eq!(cs.num_instance_variables(), 2);
            assert_eq!(cs.num_witness_variables(), 2);
            assert_eq!(cs.num_constraints(), 1);
        }

        let bn_r1cs_file_path = "test-vectors/bn128/multiply2.r1cs";
        let bls_r1cs_file_path = "test-vectors/bls12-381/multiply2.r1cs";
        let wits = vec![1, 33, 3, 11];
        let bn_wits = wits
            .iter()
            .map(|w| <Bn254 as PairingEngine>::Fr::from(*w))
            .collect::<Vec<_>>();
        let bls_wits = wits
            .iter()
            .map(|w| <Bls12_381 as PairingEngine>::Fr::from(*w))
            .collect::<Vec<_>>();

        check::<Bn254>(bn_r1cs_file_path, 0, Some(bn_wits.clone()));
        check::<Bn254>(bn_r1cs_file_path, 1, Some(bn_wits.clone()));
        check::<Bn254>(bn_r1cs_file_path, 2, Some(bn_wits.clone()));
        check::<Bls12_381>(bls_r1cs_file_path, 0, Some(bls_wits.clone()));
        check::<Bls12_381>(bls_r1cs_file_path, 1, Some(bls_wits.clone()));
        check::<Bls12_381>(bls_r1cs_file_path, 2, Some(bls_wits.clone()));
    }

    #[test]
    fn test_1() {
        fn check<E: PairingEngine>(
            r1cs_file_path: &str,
            commit_witness_count: usize,
            wits: Option<Vec<E::Fr>>,
        ) {
            let cs =
                generate_params_and_test_circuit::<E>(r1cs_file_path, commit_witness_count, wits);
            assert_eq!(cs.num_instance_variables(), 2);
            assert_eq!(cs.num_witness_variables(), 2);
            assert_eq!(cs.num_constraints(), 2);
        }

        let wits = vec![1, 35, 3, 9];
        let bn_wits = wits
            .iter()
            .map(|w| <Bn254 as PairingEngine>::Fr::from(*w))
            .collect::<Vec<_>>();
        let bls_wits = wits
            .iter()
            .map(|w| <Bls12_381 as PairingEngine>::Fr::from(*w))
            .collect::<Vec<_>>();
        check::<Bn254>("test-vectors/bn128/test1.r1cs", 1, Some(bn_wits.clone()));
        check::<Bn254>("test-vectors/bn128/test1.r1cs", 0, Some(bn_wits));
        check::<Bls12_381>(
            "test-vectors/bls12-381/test1.r1cs",
            1,
            Some(bls_wits.clone()),
        );
        check::<Bls12_381>("test-vectors/bls12-381/test1.r1cs", 0, Some(bls_wits));
    }

    #[test]
    fn test_2() {
        fn check<E: PairingEngine>(
            r1cs_file_path: &str,
            commit_witness_count: usize,
            wits: Option<Vec<E::Fr>>,
        ) {
            let cs =
                generate_params_and_test_circuit::<E>(r1cs_file_path, commit_witness_count, wits);
            assert_eq!(cs.num_instance_variables(), 2);
            assert_eq!(cs.num_witness_variables(), 4);
            assert_eq!(cs.num_constraints(), 3);
        }

        let bn_r1cs_file_path = "test-vectors/bn128/test2.r1cs";
        let bls_r1cs_file_path = "test-vectors/bls12-381/test2.r1cs";
        let wits = vec![1, 12, 1, 2, 1, 4];
        let bn_wits = wits
            .iter()
            .map(|w| <Bn254 as PairingEngine>::Fr::from(*w))
            .collect::<Vec<_>>();
        let bls_wits = wits
            .iter()
            .map(|w| <Bls12_381 as PairingEngine>::Fr::from(*w))
            .collect::<Vec<_>>();

        check::<Bn254>(bn_r1cs_file_path, 0, Some(bn_wits.clone()));
        check::<Bn254>(bn_r1cs_file_path, 1, Some(bn_wits.clone()));
        check::<Bn254>(bn_r1cs_file_path, 2, Some(bn_wits));
        check::<Bls12_381>(bls_r1cs_file_path, 0, Some(bls_wits.clone()));
        check::<Bls12_381>(bls_r1cs_file_path, 1, Some(bls_wits.clone()));
        check::<Bls12_381>(bls_r1cs_file_path, 2, Some(bls_wits));
    }

    #[test]
    fn test_3() {
        fn check<E: PairingEngine>(
            r1cs_file_path: &str,
            commit_witness_count: usize,
            wits: Option<Vec<E::Fr>>,
        ) {
            let cs =
                generate_params_and_test_circuit::<E>(r1cs_file_path, commit_witness_count, wits);
            assert_eq!(cs.num_instance_variables(), 5); // 1 + 2 outputs + 2 public inputs
            assert_eq!(cs.num_witness_variables(), 7);
            assert_eq!(cs.num_constraints(), 5);
        }

        check::<Bn254>("test-vectors/bn128/test3.r1cs", 0, None);
        check::<Bn254>("test-vectors/bn128/test3.r1cs", 1, None);
        check::<Bn254>("test-vectors/bn128/test3.r1cs", 2, None);
        check::<Bn254>("test-vectors/bn128/test3.r1cs", 3, None);
        check::<Bn254>("test-vectors/bn128/test3.r1cs", 4, None);
        check::<Bls12_381>("test-vectors/bls12-381/test3.r1cs", 0, None);
        check::<Bls12_381>("test-vectors/bls12-381/test3.r1cs", 1, None);
        check::<Bls12_381>("test-vectors/bls12-381/test3.r1cs", 2, None);
        check::<Bls12_381>("test-vectors/bls12-381/test3.r1cs", 3, None);
        check::<Bls12_381>("test-vectors/bls12-381/test3.r1cs", 4, None);
    }

    #[test]
    fn test_4() {
        fn check<E: PairingEngine>(
            r1cs_file_path: &str,
            commit_witness_count: usize,
            wits: Option<Vec<E::Fr>>,
        ) {
            let cs =
                generate_params_and_test_circuit::<E>(r1cs_file_path, commit_witness_count, wits);
            assert_eq!(cs.num_instance_variables(), 7); // 1 + 2 outputs + 4 public inputs
        }

        check::<Bn254>("test-vectors/bn128/test4.r1cs", 0, None);
        check::<Bn254>("test-vectors/bn128/test4.r1cs", 1, None);
        check::<Bn254>("test-vectors/bn128/test4.r1cs", 2, None);
        check::<Bn254>("test-vectors/bn128/test4.r1cs", 3, None);
        check::<Bn254>("test-vectors/bn128/test4.r1cs", 4, None);
        check::<Bls12_381>("test-vectors/bls12-381/test4.r1cs", 0, None);
        check::<Bls12_381>("test-vectors/bls12-381/test4.r1cs", 1, None);
        check::<Bls12_381>("test-vectors/bls12-381/test4.r1cs", 2, None);
        check::<Bls12_381>("test-vectors/bls12-381/test4.r1cs", 3, None);
        check::<Bls12_381>("test-vectors/bls12-381/test4.r1cs", 4, None);
    }

    #[test]
    fn multiply_n() {
        generate_params_and_test_circuit::<Bn254>("test-vectors/bn128/multiply_n.r1cs", 30, None);
        generate_params_and_test_circuit::<Bls12_381>(
            "test-vectors/bls12-381/multiply_n.r1cs",
            30,
            None,
        );
    }

    #[test]
    fn nconstraints() {
        generate_params_and_test_circuit::<Bn254>("test-vectors/bn128/nconstraints.r1cs", 1, None);
        generate_params_and_test_circuit::<Bls12_381>(
            "test-vectors/bls12-381/nconstraints.r1cs",
            1,
            None,
        );
    }

    #[test]
    fn multiply2_bounded() {
        generate_params_and_test_circuit::<Bn254>(
            "test-vectors/bn128/multiply2_bounded.r1cs",
            2,
            None,
        );
        generate_params_and_test_circuit::<Bls12_381>(
            "test-vectors/bls12-381/multiply2_bounded.r1cs",
            2,
            None,
        );
    }

    #[test]
    fn mimc() {
        generate_params_and_test_circuit::<Bn254>("test-vectors/bn128/mimc_bn128.r1cs", 8, None);
        generate_params_and_test_circuit::<Bls12_381>(
            "test-vectors/bls12-381/mimc_bls12_381.r1cs",
            8,
            None,
        );
    }

    #[test]
    fn mimcsponge() {
        generate_params_and_test_circuit::<Bn254>(
            "test-vectors/bn128/mimcsponge_bn128.r1cs",
            2,
            None,
        );
        generate_params_and_test_circuit::<Bls12_381>(
            "test-vectors/bls12-381/mimcsponge_bls12_381.r1cs",
            2,
            None,
        );
    }

    #[test]
    fn less_than_32_bits() {
        generate_params_and_test_circuit::<Bn254>("test-vectors/bn128/less_than_32.r1cs", 2, None);
        generate_params_and_test_circuit::<Bls12_381>(
            "test-vectors/bls12-381/less_than_32.r1cs",
            2,
            None,
        );
    }

    #[test]
    fn less_than_public_64_bits() {
        generate_params_and_test_circuit::<Bn254>(
            "test-vectors/bn128/less_than_public_64.r1cs",
            1,
            None,
        );
        generate_params_and_test_circuit::<Bls12_381>(
            "test-vectors/bls12-381/less_than_public_64.r1cs",
            1,
            None,
        );
    }

    #[test]
    fn all_different_10() {
        generate_params_and_test_circuit::<Bn254>(
            "test-vectors/bn128/all_different_10.r1cs",
            10,
            None,
        );
        generate_params_and_test_circuit::<Bls12_381>(
            "test-vectors/bls12-381/all_different_10.r1cs",
            10,
            None,
        );
    }
}
