# Testing

> **Recommended reading:** 
> [2.6: Testing](https://rust-unofficial.github.io/too-many-lists/first-test.html),

The linked chapter in the "Learning Rust With Entirely Too Many Linked Lists" tutorial explains how testing normal Rust code works. In this chapter we will check both the code and the specifications that we added in the previous chapters.

Note: Normal tests (marked with `#[cfg(test)]` or `#[test]`) are currently ***not*** checked by Prusti, but this may be added in the future. Without the `test` markers, Prusti will check any test like a normal function.

We have written some specifications in the previous chapters, but we didn't check if they are actually correct or useful. For example, a function that has a too restrictive precondition may be verified successfully by itself, but cannot be used:

```rust,noplaypen
{{#rustdoc_include ../../../../prusti-tests/tests/verify/fail/user-guide/testing_restrictive_fn.rs:code}}
```

This function is correct (ignoring potential overflows), but it is not useful, since the input must be `10`.

Another potential problem could be a disconnect in what the specification says, and what the programmer wants a function to do:

```rust,noplaypen
{{#rustdoc_include ../../../../prusti-tests/tests/verify/fail/user-guide/testing_incorrect_specs.rs:code}}
```

There is not error shown on the square function, since it will never panic (ignoring overflows again), and it does exactly what the specification says it does. Checking the specification with a test function shows however, that the function calculates `x` cubed instead of `x` squared.

For internal functions, you will likely notice mistakes in the specification when you use it in other code in your project. When you have public functions however, like for example in a library, you might want to write some tests for your specification to ensure that they are correct and useful.

## Testing our linked list specifications

To check our specifications and code, we can write a function that relies on the expected behavior. We can create a new namespace for the test, here we call it `prusti_tests`:

```rust,noplaypen
{{#rustdoc_include ../../../../prusti-tests/tests/verify/pass/user-guide/testing_initial_code.rs:test_1}}
// Prusti: verifies
```
We can also have tests that take arguments and also have pre- and postconditions:

```rust,noplaypen
{{#rustdoc_include ../../../../prusti-tests/tests/verify/pass/user-guide/testing_initial_code.rs:test_2}}
// Prusti: verifies
```

If you change any parts of this test, you will get a verification error, e.g., testing for any different lengths will cause the verification to fail.
Since this code can be verified, it appears that our specification matches our expectation for what the code does. 

## Note on differences between verification and unit tests

Static verification is stronger than unit testing, since unit tests will not be able to check the entire space of possible inputs for a function.
It might still be worth writing some unit tests even for verified code, to catch errors in the specifications. As noted above, Prusti will be able to check unit tests in the future.