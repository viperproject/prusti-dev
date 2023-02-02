# Testing

> **Recommended reading:** 
> [2.6: Testing](https://rust-unofficial.github.io/too-many-lists/first-test.html),

The linked chapter in the "Learning Rust With Entirely Too Many Linked Lists" tutorial explains how testing normal Rust code works. In this chapter we will check both the code and the specifications that we added in the previous chapters.

Note: Normal tests (marked by `#[cfg(test)]`) are currently ***not*** checked by Prusti, but this may be added in the future.

To check our specifications and code, we can write a function that relies on the expected behavior. Just like in the `Testing` chapter, we can create a new namespace for the test:

```rust,noplaypen
{{#rustdoc_include tour-src/src/testing/initial_code.rs:test_1}}
// Prusti: verifies
```
We can also have tests that take arguments and also have pre- and postconditions:

```rust,noplaypen
{{#rustdoc_include tour-src/src/testing/initial_code.rs:test_2}}
// Prusti: verifies
```

This passes as well. In this test we can see that we can call `pop` at least 4 times without the possibility of a panic, since the length of `list_0` is at least 4.

Running Prusti on the project again should still verify. If you change any parts of this test, you will get a verification error, e.g., testing for any different lengths will cause the verification to fail.

Verification should not completely replace normal testing.
A passing verification just means that the code will not panic and that it does exactly what the specifications describe.
Just like in normal code, what the code and specification encode may not be the same as what the programmer wants, and testing can help catch such missalignments.