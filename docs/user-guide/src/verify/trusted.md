# Trusted functions

Sometimes specifications express a fact which is true about a function, but the verifier cannot prove it automatically, or it uses features not yet supported by Prusti. In such cases, it is possible to mark a function as `#[trusted]`:

```rust,noplaypen,ignore
use prusti_contracts::*;

#[trusted]
#[ensures(*a == old(*b) && *b == old(*a))]
fn xor_swap(a: &mut i32, b: &mut i32) {
    *a ^= *b;
    *b ^= *a;
    *a ^= *b;
}
```

In the above example, the contract for `xor_swap` is correct, but Prusti would not be able to verify it because it uses currently unsupported XOR operations.

While a common application of `#[trusted]` is to wrap functions from the standard library or external libraries, note that [external specifications](external.md) provide a more robust solution for this use case.

## Why trusted functions are dangerous

When declaring a function as `#[trusted]`, Prusti ignores the function's body and assumes the provided pre- and postconditions have already been successfully verified.
As the example below demonstrates, a single wrong, yet trusted, specification may lead to wrong and unexpected verification results.
Hence, some care is needed to ensure that the specifications of trusted functions are indeed correct.

```rust,noplaypen,ignore
use prusti_contracts::*;

#[trusted]
#[ensures(42 == 23)] // assumed correct since we trust foo()
fn foo() { unreachable!() }

fn test() {
    foo();
    assert!(1 == 2); // verifies successfully
}
```
