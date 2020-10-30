# Basic Usage

When the Prusti Assistant extension is active, Rust files can be verified in one of the following ways:

- By clicking the "Verify with Prusti" button in the status bar.
- By saving a Rust document, if "Verify on save" is enabled.
- By opening a Rust document, if "Verify on open" is enabled.

See the [following chapter](verify/summary.md) for a list of verification features available in Prusti.

## Example

The specification for a `max` function (returning the greater of its two inputs) could be:

```rust
extern crate prusti_contracts;
use prusti_contracts::*;

#[pure]
#[ensures(result >= a && result >= b)]
#[ensures(result == a || result == b)]
fn max(a: i32, b: i32) -> i32 {
    if a > b {
        a
    } else {
        b
    }
}
```

In the above:

- The initial `extern crate prusti_contracts;` is needed by Prusti to typecheck the specifications.
- `use prusti_contracts::*;` allows `#[ensures(...)]` instead of `#[prusti_contracts::ensures(...)]`.
- `result` is a keyword for referring to the function's return value.

> Due to limitations in Rust procedural macros, `use prusti_contracts::*;` should *always* be used, and the Prusti specification attributes should not be imported with an alias.
