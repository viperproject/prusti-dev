# Prusti capabilities

- Good integration with standard Rust tooling, invokation of Prusti works in the same way as invoking Cargo or rustc
- Error messages are provided in the same way as in normal Rust compilation
  - Messages shown inlined in source code with Prusti-Assistant VSCode extension
- Code with Prusti annotations can still be compiled with normal rustc
  - Prusti annotations are automatically removed at compile time using the Rust macro system
- Prusti can verify either individual Rust files, entire Cargo projects and also Cargo workspaces containing multiple crates
- Can verify generic and non-generic functions and types
- Pre- and postconditions and `prusti_assert`s support using quantifiers (`forall`, `exists`)
