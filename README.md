**WARNING:** We are currently upgrading Prusti to work with the latest version of the Rust compiler. As a result, the version of Prusti in the `master` branch has severe regressions. If you want to see the code of Prusti that matches the version used in [Prusti Assistant](https://marketplace.visualstudio.com/items?itemName=viper-admin.prusti-assistant), you can find it at the commit tagged with `rustc-2018-06-07`.

Prusti
======

[![Test and deploy](https://github.com/viperproject/prusti-dev/workflows/Test%20and%20deploy/badge.svg)](https://github.com/viperproject/prusti-dev/actions?query=workflow%3A"Test+and+deploy"+branch%3Amaster)
[![Test on crates](https://github.com/viperproject/prusti-dev/workflows/Test%20on%20crates/badge.svg)](https://github.com/viperproject/prusti-dev/actions?query=workflow%3A"Test+on+crates"+branch%3Amaster)
[![Test coverage](https://codecov.io/gh/viperproject/prusti-dev/branch/master/graph/badge.svg)](https://codecov.io/gh/viperproject/prusti-dev)
[![Project chat](https://img.shields.io/badge/Zulip-join_chat-brightgreen.svg)](https://prusti.zulipchat.com/)

[Prusti](http://www.pm.inf.ethz.ch/research/prusti.html) is a prototype verifier for Rust,
built upon the the [Viper verification infrastructure](http://www.pm.inf.ethz.ch/research/viper.html).

By default Prusti verifies absence of panics by proving that statements such as `unreachable!()` and `panic!()` are unreachable.
Overflow checking can be enabled with a configuration flag, otherwise all integers are treated as unbounded.
In Prusti, the functional behaviour of a function can be specified by using annotations, among which are preconditions, postconditions, and loop invariants.
The tool checks them, reporting error messages when the code does not adhere to the provided specification.

For a tutorial and more information, check out [the wiki page](https://github.com/viperproject/prusti-dev/wiki).


Using Prusti
------------

The easiest way to try out Prusti is by using the ["Prusti Assistant"](https://marketplace.visualstudio.com/items?itemName=viper-admin.prusti-assistant) extension for VS Code.

Alternatively, if you wish to use Prusti from the command line there are two options:
* Download the precompiled binaries for Ubuntu, Windows, or MacOS from [the latest GitHub release](https://github.com/viperproject/prusti-dev/releases/latest).
* Compile from the source code, running `./x.py setup` and `./x.py build --release`.
