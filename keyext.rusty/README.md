# Rusty KeY

This folder contains the KeY version for Rust, implementing RustyDL.

## Installation

### Installing Rust

To run Rusty KeY, one requires Rust, Cargo, and rustup. For details see [the Rust home page](https://www.rust-lang.org/).

For a quick install of rustup, which manages all Rust utilities, run
```sh
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
```

Our setup ensures that rustup always picks the correct version of Rust to run.
This means, that executing Rusty KeY may take some additional time when it is run for the first time,
as we install a new Rust version.

### Setting up Libraries

We depend on a wrapper of the Rust compiler. Before using Rusty KeY, run
````shell
git submodule update --init --recursive
````
in the `key` folder.

## Examples & Testing

Examples can be found in [`keyext.rusty/src/test/resources/testcase/examples/`](./src/test/resources/testcase/examples/).

To run all proofs in the example folder use
```shell
./gradlew :keyext.rusty:testRunAllProofs
```