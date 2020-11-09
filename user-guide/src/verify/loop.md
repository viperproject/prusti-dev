# Loop body invariants

To verify loops, including loops in which the loop condition has side effects, Prusti allows specifying the *invariant of the loop body* using the `body_invariant!(...);` statement. The expression inside the parentheses should be a [Prusti specification](../syntax.md). There may be any number of body invariants in any given loop, but they must all be written at the beginning of the loop body.

| Feature | Status |
| --- | --- |
| Loop conditions without side-effects | Supported |
| Loop conditions with side-effects | Supported |
| Loops with `break`, `continue`, or `return` statements | Supported |
| Loans that cross a loop boundary (e.g. loans defined outside the loop, expiring in the loop) | Not supported yet |

In general, given the loop:

```rust
while {
  G; // possibly side-effectful
  g // loop condition
} {
  body_invariant!(I); // loop body invariant
  B // loop body
}
```

Prusti checks the following:

1. The first time that `G` has been executed, if `g` evaluates to `true` then the property `I` must hold.
2. Assuming that the property `I` holds, after executing `B; G`, if `g` evaluates to `true` then `I` must hold (again).

After the loop, Prusti knows that the program is in a state in which the loop condition evaluated to `false`. This can happen for two reasons:

1. The loop body has never been executed, because the first evaluation of the loop condition resulted in `false`. In this case, the invariant in the loop body is never reached.
2. The loop executed at least one iteration, then after executing `B` the evaluation of `{ G; g }` resulted in `false`.

Finally, the loop body invariant is not enforced when exiting from a loop with a `break` or `return` statement.

As an example, consider the following program. The loop condition calls `test_and_increment`, and the call has side effects:

```rust
extern crate prusti_contracts;
use prusti_contracts::*;

#[ensures(result == (old(*i) >= 0))]
#[ensures(*i == 1 + old(*i))]
fn test_and_increment(i: &mut usize) -> bool {
    let old_i = *i;
    *i += 1;
    old_i >= 0
}

#[requires(*i > 0)]
fn work(i: &mut usize) {
    // ...
}

fn main() {
    let mut i = 0;

    while test_and_increment(&mut i) {
        body_invariant!(i > 0);
        work(i);
    }

    assert!(i <= 0);
}
```

We can assert `i <= 0` after the loop, because in the last evaluation of the loop condition `i >= 0` was `false`, and `i` was then incremented by one.

Note that it would be wrong to assert `i < 0` after the loop, because it is possible to have `i == 0`. Note also that the loop body invariant `i >= 0` is not strong enough to verify the program, since `work` requires `i > 0`. In fact, after `test_and_increment` returns `true`, `i` cannot be `0` because of the `+= 1`.
