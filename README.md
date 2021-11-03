Prusti
======

[![Test](https://github.com/viperproject/prusti-dev/workflows/Test/badge.svg)](https://github.com/viperproject/prusti-dev/actions?query=workflow%3A"Test"+branch%3Amaster)
[![Test on crates](https://github.com/viperproject/prusti-dev/workflows/Test%20on%20crates/badge.svg)](https://github.com/viperproject/prusti-dev/actions?query=workflow%3A"Test+on+crates"+branch%3Amaster)
[![Deploy](https://github.com/viperproject/prusti-dev/workflows/Deploy/badge.svg)](https://github.com/viperproject/prusti-dev/actions?query=workflow%3A"Deploy"+branch%3Amaster)
[![Docker Build Status](https://img.shields.io/docker/cloud/build/viperproject/prusti)](https://hub.docker.com/r/viperproject/prusti)
[![Test coverage](https://codecov.io/gh/viperproject/prusti-dev/branch/master/graph/badge.svg)](https://codecov.io/gh/viperproject/prusti-dev)
[![Project chat](https://img.shields.io/badge/Zulip-join_chat-brightgreen.svg)](https://prusti.zulipchat.com/)

[Prusti](http://www.pm.inf.ethz.ch/research/prusti.html) is a prototype verifier for Rust,
built upon the the [Viper verification infrastructure](http://www.pm.inf.ethz.ch/research/viper.html).

By default Prusti verifies absence of integer overflows and panics by proving that statements such as `unreachable!()` and `panic!()` are unreachable.
Overflow checking can be disabled with a configuration flag, treating all integers as unbounded.
In Prusti, the functional behaviour of a function can be specified by using annotations, among which are preconditions, postconditions, and loop invariants.
The tool checks them, reporting error messages when the code does not adhere to the provided specification.

For a tutorial and more information, check out the [user guide](https://viperproject.github.io/prusti-dev/user-guide/).


Using Prusti
------------

The easiest way to try out Prusti is by using the ["Prusti Assistant"](https://marketplace.visualstudio.com/items?itemName=viper-admin.prusti-assistant) extension for VS Code.

Alternatively, if you wish to use Prusti from the command line there are three options:
* Download the precompiled binaries for Ubuntu, Windows, or MacOS from a [GitHub release](https://github.com/viperproject/prusti-dev/releases).
* Use the [`viperproject/prusti`](https://hub.docker.com/r/viperproject/prusti) Docker image.
* Compile from the source code, by installing [rustup](https://rustup.rs/), running `./x.py setup` and then `./x.py build --release`.

All three options provide the `prusti-rustc` and `cargo-prusti` programs that can be used analogously to, respectively, `rustc` and `cargo check`.
For more detailed instructions, refer to the [user guide](https://viperproject.github.io/prusti-dev/user-guide/) and to the [developer guide](https://viperproject.github.io/prusti-dev/dev-guide/).

Do you still have questions? Open an issue or contact us on [Zulip](https://prusti.zulipchat.com/).
