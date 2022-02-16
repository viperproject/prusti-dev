# Specification entailments

> **NOT YET SUPPORTED:** This feature is not yet supported in Prusti. See [PR #138](https://github.com/viperproject/prusti-dev/pull/138) for the status of this feature as well as a prototype. The syntax described here is subject to change.

The contract for a closure or function pointer variable can be given using the specification entailment syntax:

```rust
extern crate prusti_contracts;
use prusti_contracts::*;

#[requires(
  f |= |a: i32, b: i32| [
    requires(a == 5),
    requires(b == 4),
    ensures(result > 4)
  ]
)]
fn example<F: Fn (i32, i32) -> i32> (f: F) { ... }
```

In the above example, `f`, the argument to `example`, must be a function that takes two `i32` arguments. A call to `f` inside the body of `example` is only valid if the preconditions are satisfied, and the result of that call must satisfy the postcondition given.

> TODO:
>
> - arrow syntax (`~~>`)
> - ghost arguments
> - history invariants
> - multiple-call specification entailment
