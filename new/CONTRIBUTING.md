# Contributing

## Setup

Install the necessary components:

```bash
rustup component add rust-src
rustup component add rustc-dev
```

## Design

## Crates

+ `prusti` – Prusti itself.
+ Specification parsing:
  + The procedural macro crates that provide only the procedural macro entry points and no serious logic:
    + `prusti-contracts` – a crate that exposes the user facing procedural macros such as `#[requires(...)]`, `#[ensures(...)]`, and `invariant!(...)`. These macros generate `#[prusti::*]` attributes.
    + `prusti-contracts-impl` – Rust does not allow yet having `invariant!(...)` style macros in statement positions; therefore, we use [proc-macro-hack](https://crates.io/crates/proc-macro-hack) to work-around this. This crate provides the impl part of the `invariant!(...)` macro.
    + `prusti-contracts-internal` – a crate that provides a single procedural macro that takes the entire crate with `#[prusti::*]` attributes and generates the necessary additional code items for typechecking specifications.
  + `prusti-specs` – the actual implementation logic that is exposed through `prusti-contracts` and `prusti-contracts-internal`.

## Components

+ `prusti` – the Prusti itself.
+ Procedural macros – macros for various contracts' crates that rewrite their contracts to use Prusti specific attributes (`prusti::*`). `prusti` replaces the original crates providing the contracts' procedural macros with our crates.
+ `cargo prusti` uses [cargo_metadata](https://docs.rs/cargo_metadata/0.10.0/cargo_metadata/) to detect the procedural macro replacements that need to be passed into `prusti`.

## Flow

1. Detect what contracts' crates are being loaded and replace them with our versions.
2. Call the rustc_driver with two callbacks:
   1. After expansion: rewrite the specs so that the compiler typechecks and resolves the types for us.
   2. After analysis: construct Salsa and verify the program.
