# Loop Invariants

To show how to verify loops, we will use a different example than our linked list for simplicity.
We will write and verify a function that can add some value to every element of an array slice.

Let's write a function that takes an integer `x` and sums up all values from 0 to that value in a loop.
For non-negative inputs, the result will be equal to `x * (x + 1) / 2`:

```rust,noplaypen
{{#rustdoc_include ../../../../prusti-tests/tests/verify/fail/user-guide/loop_invariants.rs:specification}}
// Prusti: fails
```

We cannot verify this code yet, because Prusti does not know what the `while` loop does to `sum` and `i`. For that, we need to add a [`body_invariant`](../verify/loop.md). Body invariants are expressions that always hold at the beginning and end of the loop body. In our case, the invariant is that `sum` contains the sum of all values between 1 and `i`. Since `i` starts at 1 and not at 0, we have to slightly adjust the formula by using `i - 1` instead of `i`, so we get: `sum == (i - 1) * i / 2`.

After adding the `body_invariant`, we get this code:

```rust,noplaypen
{{#rustdoc_include ../../../../prusti-tests/tests/verify/pass/user-guide/loop_invariants_final.rs:specification}}
// Prusti: verifies
```

This body invariant is enough to verify the postcondition. After the loop, `i == x + 1` will hold. Plugging this into our `body_invariant!(sum == (i - 1) * i / 2)`, we get `sum == x * (x + 1) / 2`, which is our postcondition.

Note that we did not have to add `body_invariant!(1 <= i && i <= x)`. In some cases, such as when the loop condition is side-effect free, Prusti adds the loop condition to the body invariant, as long as at least one `body_invariant` is syntactically present in the loop.
