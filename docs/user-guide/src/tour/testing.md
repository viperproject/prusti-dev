# Testing

> **Recommended reading:** 
> [2.6: Testing](https://rust-unofficial.github.io/too-many-lists/first-test.html),

The linked chapter in the "Learning Rust With Entirely Too Many Linked Lists" tutorial explains how testing normal Rust code works. In this chapter we will show some differences between testing and verification and of the guarantees that each provides.

Note: Normal tests (marked with `#[cfg(test)]` or `#[test]`) are currently ***not*** checked by Prusti, but this may be added in the future. If you remove the `test` markers, Prusti will check any test like it would a normal function.

## Differing guarantees of verification and testing

Static verification has stronger guarantees than testing.
Running tests is only be possible for a small subset of all possible input values.
Take as an example a function taking a single value of type `u64`. The range of potential inputs is `0` to `2^64 - 1`, or `2^64` total values. Assuming each value takes 1 nano-second to test, it would take approximately `584.5` years to exhaustively test just this single function.
<!-- (2^64)/1000000000 / 60 / 60 / 24 / 365.25 = 584.54204609062639795168200370117 -->

In contrast, a static verifier like Prusti is able to check the entire input space of a function with the help of the specifications of each function.

When verification succeeds, you are guaranteed to not have a bug like a crash, overflow, or return value not fitting the specification.
This assumes that you have manually verified any `#[trusted]` functions and have checked for correct termination of all functions.
If the verification fails, you may have a bug, or your specifications are not strong enough.

The guarantees of testing are different. If a test fails, you know that you have a bug (either in the code or the test), but if all your tests pass, you might still have some bugs, just not with the specific inputs used in the tests.

In other words: Testing can show the *presence* of bugs, verification can show the *absence* of bugs.

It might still be worth writing (and running) some unit tests even for verified code, as they can serve as documentation on using a function. If you made some mistake in both the code and the specification, you may notice it if you write a test for it or use that function in another verified function.

The next section shows some potential issues with specifications.




## Examples of bugs in specifications

<!-- We have written some specifications in the previous chapters, but we didn't check if they are actually correct or useful. For example, a -->
The specification for a function could have a precondition that is too restrictive. If you never use the function in another verified function, you may not notice this:

```rust,noplaypen
{{#rustdoc_include ../../../../prusti-tests/tests/verify/fail/user-guide/testing_restrictive_fn.rs:code}}
```

This function is correct (ignoring potential overflows), but it is not useful, since the input must be `10`.

Another potential problem could be an incomplete postcondition. The `abs` function below should return the absolute value of `x`, but it only works for positive values. The verification will still succeed, because the postcondition does not specify the result for `x < 0`:

```rust,noplaypen
{{#rustdoc_include ../../../../prusti-tests/tests/verify/fail/user-guide/testing_incorrect_specs.rs:code}}
```

This bug will be noticed as soon as you try using `abs` with a negative input.
For functions internal to a project, you will likely notice mistakes in the specification when you try to use the function in other code. However, when you have public functions, like for example in a library, you might want to write some test functions for your specification. Specification errors sometimes only show up when they are actually used.



## Testing our linked list specifications

To check our specifications and code, we could write a function that relies on the expected behavior. We can create a new namespace for the test, here we call it `prusti_tests`:

```rust,noplaypen
{{#rustdoc_include ../../../../prusti-tests/tests/verify/pass/user-guide/testing_initial_code.rs:test_1}}
// Prusti: verifies
```
<!-- We can also have tests that take arguments and also have pre- and postconditions:

```rust,noplaypen
{{#rustdoc_include ../../../../prusti-tests/tests/verify/pass/user-guide/testing_initial_code.rs:test_2}}
// Prusti: verifies
``` -->

Note the `#[cfg(prusti)]` on the module `prusti_tests`. This makes the module only available during verification, with no effect during normal compilation, similar to `#[cfg(test)]` for unit tests.


Our test code can be verified, so it appears that our specification is not too restrictive or incomplete.
