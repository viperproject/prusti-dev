# Repository Layout

This section describes the crates located in the Prusti repository, their function, and key modules. Some important files are linked and described individually, although this list is far from complete.

## Binaries

These crates relate to the runnable executables produced during compilation.

 - [`prusti/`](https://github.com/viperproject/prusti-dev/tree/9ca9cd1b9bcfd9870691fa5a7a957a90987ba4af/prusti)
   - [`src/bin/prusti-driver.rs`](https://github.com/viperproject/prusti-dev/blob/9ca9cd1b9bcfd9870691fa5a7a957a90987ba4af/prusti/src/bin/prusti-driver.rs) - invokes the Rust compiler with Prusti callbacks set up.
   - [`src/bin/prusti-rustc.rs`](https://github.com/viperproject/prusti-dev/blob/9ca9cd1b9bcfd9870691fa5a7a957a90987ba4af/prusti/src/bin/prusti-rustc.rs) - spawns `prusti-driver` with the correct environment.
 - [`prusti-launch/`](https://github.com/viperproject/prusti-dev/tree/9ca9cd1b9bcfd9870691fa5a7a957a90987ba4af/prusti-launch) - utilities for Prusti binaries.
 - [`prusti-server/`](https://github.com/viperproject/prusti-dev/tree/9ca9cd1b9bcfd9870691fa5a7a957a90987ba4af/prusti-server) - [Prusti compilation server](pipeline/viper.md#prusti-server).

## Specification parsing

These crates relate to parsing Prusti-specific specifications in Rust code (e.g. `requires`, `ensures`, etc). These specifications are defined using [procedural macros](https://doc.rust-lang.org/reference/procedural-macros.html), which must be contained in their own crates, hence the additional `prusti-contracts*` crates.

 - [`prusti-contracts/`](https://github.com/viperproject/prusti-dev/tree/9ca9cd1b9bcfd9870691fa5a7a957a90987ba4af/prusti-contracts) - stubs for Rust pseudo-functions used in specifications; currently `old` and `before_expiry`. It also reexports the procedural macros `requires`, `ensures`, etc. Depending on the `prusti` feature, it exports either `impl` or `internal`.
 - [`prusti-contracts-impl/`](https://github.com/viperproject/prusti-dev/tree/9ca9cd1b9bcfd9870691fa5a7a957a90987ba4af/prusti-contracts-impl) – empty definitions of procedural macros intended to be used when compiling with the regular compiler.
 - [`prusti-contracts-internal/`](https://github.com/viperproject/prusti-dev/tree/9ca9cd1b9bcfd9870691fa5a7a957a90987ba4af/prusti-contracts-internal) - a procedural macro crate that forwards calls to `prusti-specs`.
 - [`prusti-specs/`](https://github.com/viperproject/prusti-dev/tree/9ca9cd1b9bcfd9870691fa5a7a957a90987ba4af/prusti-specs) - does the specification rewriting.
 - [`prusti-contracts-test`](https://github.com/viperproject/prusti-dev/tree/9ca9cd1b9bcfd9870691fa5a7a957a90987ba4af/prusti-contracts-test) – a minimal test that checks that `prusti-contracts` can be used with a regular compiler.

## Common library code

These crates contain the majority of Prusti's code.

 - [`prusti-common/`](https://github.com/viperproject/prusti-dev/tree/9ca9cd1b9bcfd9870691fa5a7a957a90987ba4af/prusti-common) - common modules used across Prusti (code independent from Rust internals).
   - [`src/vir/`](https://github.com/viperproject/prusti-dev/tree/9ca9cd1b9bcfd9870691fa5a7a957a90987ba4af/prusti-common/src/vir) - VIR.
     - [`ast/`](https://github.com/viperproject/prusti-dev/tree/9ca9cd1b9bcfd9870691fa5a7a957a90987ba4af/prusti-common/src/vir/ast) - Viper IR enum definitions and methods to generate Viper code (as text).
     - [`optimizations/`](https://github.com/viperproject/prusti-dev/tree/9ca9cd1b9bcfd9870691fa5a7a957a90987ba4af/prusti-common/src/vir/optimizations) - optimizations of Viper IR.
     - [`borrows.rs`](https://github.com/viperproject/prusti-dev/blob/9ca9cd1b9bcfd9870691fa5a7a957a90987ba4af/prusti-common/src/vir/borrows.rs) - reborrowing DAG definition.
     - [`conversions.rs`](https://github.com/viperproject/prusti-dev/blob/9ca9cd1b9bcfd9870691fa5a7a957a90987ba4af/prusti-common/src/vir/conversions.rs) - implicit casts from Rust types to Viper IR.
     - [`program.rs`](https://github.com/viperproject/prusti-dev/blob/9ca9cd1b9bcfd9870691fa5a7a957a90987ba4af/prusti-common/src/vir/program.rs) - struct holding a full Viper program.
     - [`to_viper.rs`](https://github.com/viperproject/prusti-dev/blob/9ca9cd1b9bcfd9870691fa5a7a957a90987ba4af/prusti-common/src/vir/to_viper.rs) - conversion of `vir` module structs to Viper AST.
     - [`utils.rs`](https://github.com/viperproject/prusti-dev/blob/9ca9cd1b9bcfd9870691fa5a7a957a90987ba4af/prusti-common/src/vir/utils.rs) - functional operations on VIR.
   - (+ other utility code)
 - [`prusti-interface/`](https://github.com/viperproject/prusti-dev/tree/9ca9cd1b9bcfd9870691fa5a7a957a90987ba4af/prusti-interface) - wrapper around the Rust compiler internals that aims to provide a more stable interface (however, it fails to **completely** encapsulate the Rust compiler from its clients).
   - [`src/environment/`](https://github.com/viperproject/prusti-dev/tree/9ca9cd1b9bcfd9870691fa5a7a957a90987ba4af/prusti-interface/src/environment) - most of the wrapper code lives here.
   - [`src/specs/`](https://github.com/viperproject/prusti-dev/tree/9ca9cd1b9bcfd9870691fa5a7a957a90987ba4af/prusti-interface/src/specs) – collect type-checked specifications.
 - [`prusti-viper/`](https://github.com/viperproject/prusti-dev/tree/9ca9cd1b9bcfd9870691fa5a7a957a90987ba4af/prusti-viper) - MIR to VIR encoding.

## JVM bindings

- [`viper-sys`](https://github.com/viperproject/prusti-dev/tree/9ca9cd1b9bcfd9870691fa5a7a957a90987ba4af/viper-sys) – low-level (unsafe) JVM bindings.
- [`viper`](https://github.com/viperproject/prusti-dev/tree/9ca9cd1b9bcfd9870691fa5a7a957a90987ba4af/viper) – higher-level JVM bindings.

## Deprecated or removed

 - `prusti-filter/` - walks through Rust crates to check which are supported by Prusti (used for evaluation in Prusti publication).
 - `prusti-macros/` - macros to simplify parsing code.
