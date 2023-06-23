# Counterexamples

Let's take the summation function from the [Loop invariants](loop_invariants.md) chapter, which adds up all the numbers from 1 to `x`. Let's suppose we forgot to add the non-negativity postcondition for `x`:

```rust,noplaypen
{{#rustdoc_include ../../../../prusti-tests/tests/verify/fail/user-guide/counterexample.rs:code}}
```

Attempting to verify this file will result in an error:
```plain
[Prusti: verification error] postcondition might not hold.
```

One way to help with debugging such a verification failure, is to have Prusti print a **counterexample**. This can be enabled by adding the `counterexample = true` flag in the `Prusti.toml` file.

A counterexample is any combination of values, which will cause some postcondition or assertion to fail (there are no guarantees on which values get chosen).

After running Prusti again with the new setting, we will get an error message like this one:
```plain
[Prusti: verification error] postcondition might not hold.
    final_code.rs(12, 1): the error originates here
    final_code.rs(12, 14): counterexample for "x"
        initial value: ?
        final value: -2
    final_code.rs(13, 9): counterexample for "i"
        final value: 1
    final_code.rs(14, 9): counterexample for "sum"
        final value: 0
    final_code.rs(12, 25): counterexample for result
        final value: 0
```

Here we can see that the postcondition does not hold for `x == -2`, which will result in final values of `i == 1`, `sum == 0` and `result == 0`. This should help with finding wrong specifications or bugs in the code, which in this case is allowing negative numbers as an input.


Note that verification with `counterexample = true` is slower than normal verification.
