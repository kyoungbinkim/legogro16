# Circom integration

Build a circuit from R1CS file and generate witnesses from given inputs and WASM file.

Supports only Circom 2 and curves BN128 and BLS12-381 for now. 

Most of the code to parse r1cs and wasm files has been taken from [here](https://github.com/gakonst/ark-circom) and [here](https://github.com/iden3/circom_runtime/blob/master/js/witness_calculator.js)

## Build

```
cargo build --features=circom
```

For no_std

```
cargo build --no-default-features --features=circom
```

## Test

Tests are run for 2 curves, `bn128` and `bls12-381`. The circuits used in the tests are present in [circuits](../../test-vectors/circuits) 
directory and the `.wasm` and `.r1cs` files for both curves are present in their respective directories, for [bn128](../../test-vectors/bn128) 
and [bls12-381](../../test-vectors/bls12-381). 