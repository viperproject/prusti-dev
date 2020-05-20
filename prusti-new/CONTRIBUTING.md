# Setup

Install the necessary components:

```bash
rustup component add rust-src
rustup component add rustc-dev
```

# Design

## Components

+ `prusti` – the Prusti itself.
+ Procedural macros – macros for various contracts' crates that rewrite their contracts to use Prusti specific attributes (`prusti::*`). `prusti` replaces the original crates providing the contracts' procedural macros with our crates.

## Flow

1. Detect what contracts' crates are being loaded and replace them with our versions.
2. Call the rustc_driver with two callbacks:
   1. After expansion: rewrite the specs so that the compiler typechecks and resolves the types for us.
   2. After analysis: construct Salsa and verify the program.
