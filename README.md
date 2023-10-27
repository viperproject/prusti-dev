Prusti
======

[![Test](https://github.com/viperproject/prusti-dev/actions/workflows/test.yml/badge.svg?branch=master)](https://github.com/viperproject/prusti-dev/actions/workflows/test.yml?query=branch%3Amaster)
[![Deploy](https://github.com/viperproject/prusti-dev/actions/workflows/deploy.yml/badge.svg?branch=master)](https://github.com/viperproject/prusti-dev/actions/workflows/deploy.yml?query=branch%3Amaster)
[![Test coverage](https://codecov.io/gh/viperproject/prusti-dev/branch/master/graph/badge.svg)](https://codecov.io/gh/viperproject/prusti-dev)
[![Project chat](https://img.shields.io/badge/Zulip-join_chat-brightgreen.svg)](https://prusti.zulipchat.com/)

[Prusti](http://www.pm.inf.ethz.ch/research/prusti.html) is a prototype verifier for Rust that makes it possible to formally prove absence of bugs and correctness of code contracts. Internally, Prusti builds upon the [Viper verification infrastructure](http://www.pm.inf.ethz.ch/research/viper.html).

By default Prusti verifies absence of integer overflows and panics, proving that statements such as `unreachable!()` and `panic!()` are unreachable.
Overflow checking can be disabled with a configuration flag, treating all integers as unbounded.
In Prusti, the functional behaviour of functions and external libraries can be specified by using annotations, among which are preconditions, postconditions, and loop invariants.
The tool checks them, reporting error messages when the code does not adhere to the provided specification.

Useful links
------------

* 💻 [VS Code extension](https://marketplace.visualstudio.com/items?itemName=viper-admin.prusti-assistant) to use Prusti from your IDE.
* 📖 [User guide](https://viperproject.github.io/prusti-dev/user-guide/), containing installation instructions, a guided tutorial and a description of various verification features.
* 🧰 [Developer guide](https://viperproject.github.io/prusti-dev/dev-guide/), meant for new contributors. If you wonder how to help, give a look at the [good first issues](https://github.com/viperproject/prusti-dev/issues?q=is%3Aopen+is%3Aissue+label%3A%22good+first+issue%22).
* 📚 [List of publications](http://www.pm.inf.ethz.ch/research/prusti.html). To cite the Prusti verifier, please use [this BibTeX entry](http://pm.inf.ethz.ch/publications/getbib.php?action=bibtex&bibname=Own&id=AstrauskasMuellerPoliSummers19b).
* ⚖️ [License](https://github.com/viperproject/prusti-dev/blob/master/LICENSE) of the source code (Mozilla Public License Version 2.0, with exceptions).
* 💬 Do you still have questions? Open an issue or contact us on the [Zulip chat](https://prusti.zulipchat.com/).

Getting Prusti
--------------

The easiest way to try out Prusti is by using the ["Prusti Assistant"](https://marketplace.visualstudio.com/items?itemName=viper-admin.prusti-assistant) extension for VS Code. See the **requirements** and the troubleshooting section in its [readme](https://github.com/viperproject/prusti-assistant/blob/master/README.md).

Alternatively, if you wish to use Prusti from the command line there are three options:
* Download the precompiled binaries for Ubuntu, Windows, or macOS x64 from a [GitHub release](https://github.com/viperproject/prusti-dev/releases).
* Compile from the source code, by installing [rustup](https://rustup.rs/), running `./x.py setup` and then `./x.py build --release`.
* (unmaintained) Build a Docker image from this [`Dockerfile`](Dockerfile).

All three options provide the `prusti-rustc` and `cargo-prusti` programs that can be used analogously to, respectively, `rustc` and `cargo build`.
For more detailed instructions, refer to the guides linked above.


Quick example
-------------

1. Take the following program:
    ```rust
    /// A monotonically increasing discrete function, with domain [0, domain_size)
    trait Function {
      fn domain_size(&self) -> usize;
      fn eval(&self, x: usize) -> i32;
    }

    /// Find the `x` s.t. `f(x) == target`
    fn bisect<T: Function>(f: &T, target: i32) -> Option<usize> {
      let mut low = 0;
      let mut high = f.domain_size();
      while low < high {
        let mid = (low + high) / 2;
        let mid_val = f.eval(mid);
        if mid_val < target {
          low = mid + 1;
        } else if mid_val > target {
          high = mid;
        } else {
          return Some(mid)
        }
      }
      None
    }
    ```
2. Run Prusti. You get the following error:
    ```
    error: [Prusti: verification error] assertion might fail with "attempt to add with overflow"
      --> example.rs:12:15
       |
    12 |     let mid = (low + high) / 2;
       |               ^^^^^^^^^^^^

    Verification failed
    ```
3. Fix the buggy line with `let mid = low + ((high - low) / 2);`
4. Run Prusti. Now the `bisect` function verifies.

Congratulations! You just proved absence of panics and integer overflows in the `bisect` function. To additionally prove that the result is correct (i.e. such that `f(x) == target`), see [this example](https://github.com/viperproject/prusti-dev/blob/master/prusti-tests/tests/verify_overflow/pass/overflow/bisect.rs).
