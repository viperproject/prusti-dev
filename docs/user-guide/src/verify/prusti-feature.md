# Conditional compilation for verification vs normal compilation

Some functions are intended to only be used during verification, but not be part of normal compilation.
Prusti sets the `prusti` feature during verification, which can be use to conditionally include code:

```rust,noplaypen
# // The next line is only required for doctests, you can ignore/remove it
# extern crate prusti_contracts;
use prusti_contracts::*;

#[cfg(prusti)]
fn prusti_test() {
    // Write some code that should be verified,
    // but not compiled
    // ...
}
```