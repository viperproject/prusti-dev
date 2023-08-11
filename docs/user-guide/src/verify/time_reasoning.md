# Time reasoning

With the setting [`TIME_REASONING=true`](https://viperproject.github.io/prusti-dev/dev-guide/config/flags.html#time_reasoning), two built-in [resources](resources_obligations.md) are available: `time_credits` and `time_receipts`. They can be used to prove lower and upper bounds on the running time of functions.

For the most part, they behave as any other resource defined by the user using the [`resource!` macro](resources_obligations.md). However, they are special in that at the beginning of every function and in every loop iteration (specifically, right after the [loop invariant](loop.md)), one instance of `time_credits` is consumed and one instance of `time_receipts` is produced. If enough `time_credits` might not be available, verification fails with an error.

Since the number of `time_credits` asserted in a function's precondition is an upper bound on the number of `time_credits` consumed inside the function, it serves as an upper bound on the running time of the function. Similarly, asserting a certain number of `time_receipts` in the postcondition entails a lower bound on the function's running time.

In the following example, we make these two bounds match and therefore show that the function always needs exactly `n + 1` time steps to execute.

```rust,noplaypen
{{#rustdoc_include ../../../../prusti-tests/tests/verify/pass/user-guide/time_loop.rs:code}}
// Prusti: VERIFIES
```

The number of time steps a function needs to execute might also depend on the input in more complicated ways. See the next example.

```rust,noplaygen
{{#rustdoc_include ../../../../prusti-tests/tests/verify/pass/user-guide/time_more_complicated.rs:code}}
// Prusti: VERIFIES
```

The following are three more equivalent ways of specifying the same precondition of `do_work` as above.

```rust,noplaygen,ignore
#[requires(time_credits(6))]
#[requires(if more_work { time_credits(5) } else { true })]
fn do_work(more_work: bool) {
    // ...
}
```

```rust,noplaypen,ignore
#[requires(time_credits(6) & (more_work ==> time_credits(5)))]
fn do_work(more_work: bool) {
    // ...
}
```

```rust,noplaypen,ignore
#[requires(more_work ==> time_credits(11))]
#[requires(!more_work ==> time_credits(6))]
fn do_work(more_work: bool) {
    // ...
}
```

## Pure functions

[NOT FULLY IMPLEMENTED YET, MIGHT CHANGE IN FUTURE] `time_credits` and `time_receipts` may not appear in preconditions and postconditions of [`#[pure]`](pure.md) functions. For the purposes of time reasoning, the execution of pure functions is taken to be instantaneous: they do not produce or consume any `time_credits` or `time_receipts`.
