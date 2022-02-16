# Closures

> **NOT YET SUPPORTED:** This feature is not yet supported in Prusti. See [PR #138](https://github.com/viperproject/prusti-dev/pull/138) for the status of this feature as well as a prototype. The syntax described here is subject to change.

[Rust closures](https://doc.rust-lang.org/book/ch13-01-closures.html) can be given a specification using the `closure!(...)` syntax:

```rust
extern crate prusti_contracts;
use prusti_contracts::*;

fn main() {
    let cl = closure!(
        requires(a > b),
        ensures(result > b),
        |a: i32, b: i32| -> i32 { a }
    );
}
```

`closure!` can have any number of pre- and postconditions. The arguments and return type for the closure must be given explicitly. See [specification entailments](spec_ent.md) for specifying the contract of a higher-order function (e.g. when taking a closure as an argument).
