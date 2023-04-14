<h1 align="center"> 경빈🛠️ </h1>
https://github.com/kyoungbinkim/legogro16/blob/comm-wit/test-vectors/circuits/range_proof.circom : range_proof circom code 추가

https://github.com/kyoungbinkim/legogro16/blob/comm-wit/src/circom/tests.rs#L137 : range_proof code 추가
https://github.com/kyoungbinkim/legogro16/blob/comm-wit/src/circom/tests.rs#L894 : BN128 (BN254) Test code
https://github.com/kyoungbinkim/legogro16/blob/comm-wit/src/circom/tests.rs#L902 : BLS12-381 Test code

<h2 align="center"> 실험결과 </h2>

### 실험환경 macbook Pro M1 32G RAM
<p align="center">
    <img src="./BN-128-Test.png"/>
    BN128 (BN254) 실험결과 : proving time 6~7ms
    <br/><br/><br/><br/>
    <img src="./BLS12-381-Test.png"/>
    BLS12-381 실험결과 : proving time 8ms
    <br/><br/><br/><br/>
</p>

<h1 align="center">legogroth16</h1>

<p align="center">
    <img src="https://github.com/arkworks-rs/groth16/workflows/CI/badge.svg?branch=master">
    <a href="https://github.com/arkworks-rs/groth16/blob/master/LICENSE-APACHE"><img src="https://img.shields.io/badge/license-APACHE-blue.svg"></a>
    <a href="https://github.com/arkworks-rs/groth16/blob/master/LICENSE-MIT"><img src="https://img.shields.io/badge/license-MIT-blue.svg"></a>
    <a href="https://deps.rs/repo/github/arkworks-rs/groth16"><img src="https://deps.rs/repo/github/arkworks-rs/groth16/status.svg"></a>
</p>

The arkworks ecosystem consist of Rust libraries for designing and working with __zero knowledge succinct non-interactive arguments (zkSNARKs)__. 
This repository contains an implementation of the LegoGroth16, the [LegoSNARK](https://eprint.iacr.org/2019/142) variant of [Groth16](https://eprint.iacr.org/2016/260) zkSNARK proof system.  
This project started as fork of [this](https://github.com/kobigurk/legogro16) but is updated to 
- commit to a subset of the witnesses by specifying the count, say `n`, of the witnesses to commit during CRS generation. 
  By convention, it commits to the first `n` variables allocated for witnesses in the circuit and the proof contains that commitment
- either contain CP_link as well or omit it but only have the proof contain the commitment. The proof here contains 2 commitments (one is same as above)
  to the witness variables but with different commitment keys and randomness. 

The zkSNARK for Linear Subspaces from appendix D of LegoSNARK paper is [here](src/link/snark.rs).


This library is released under the MIT License and the Apache v2 License (see [License](#license)).

**WARNING:** This is an academic proof-of-concept prototype, and in particular has not received careful code review. This implementation is NOT ready for production use.

## Build guide

The library compiles on the `stable` toolchain of the Rust compiler. To install the latest version of Rust, first install `rustup` by following the instructions [here](https://rustup.rs/), or via your platform's package manager. Once `rustup` is installed, install the Rust toolchain by invoking:
```bash
rustup install stable
```

After that, use `cargo`, the standard Rust build tool, to build the library:
```bash
git clone https://github.com/lovesh/legogroth16
cargo build --release
```

This library comes with unit tests for each of the provided crates. Run the tests with:
```bash
cargo test
```

To build without `std` but with Circom support and proof aggregation, run 
```
cargo build --no-default-features --features=circom,aggregation,wasmer-sys
```

To build for WASM with Circom support and proof aggregation, run
```
cargo build --no-default-features --features=circom,aggregation,wasmer-js --target wasm32-unknown-unknown
```

To run all tests without `std`, run
```
cargo test --no-default-features --features=std,circom,aggregation,wasmer-sys
```

## License

This library is licensed under either of the following licenses, at your discretion.

 * Apache License Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

Unless you explicitly state otherwise, any contribution submitted for inclusion in this library by you shall be dual licensed as above (as defined in the Apache v2 License), without any additional terms or conditions.

## Acknowledgements

This work was supported by:
a Google Faculty Award;
the National Science Foundation;
the UC Berkeley Center for Long-Term Cybersecurity;
and donations from the Ethereum Foundation, the Interchain Foundation, and Qtum.

An earlier version of this library was developed as part of the paper *"[ZEXE: Enabling Decentralized Private Computation][zexe]"*.

[zexe]: https://ia.cr/2018/962
