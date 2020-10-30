# Trusted functions

Sometimes specifications express a fact which is true about a function, but the verifier cannot prove it automatically, or it uses features not yet supported by Prusti. In such cases, it is possible to mark a function `#[trusted]`:

```rust
extern crate prusti_contracts;
use prusti_contracts::*;

#[trusted]
#[ensures(*a == old(*b) && *b == old(*a))]
fn xor_swap(a: &mut i32, b: &mut i32) {
    *a ^= *b;
    *b ^= *a;
    *a ^= *b;
}
```

In the above example, the contract for `xor_swap` is correct, but Prusti would not be able to verify it because it uses an XOR operation.

When using `#[trusted]`, care should be taken in ensuring that the specification is correct. It is possible to use `#[trusted]` to wrap functions from the standard library or external libraries, but see [external specifications](external.md) for a more robust solution.
