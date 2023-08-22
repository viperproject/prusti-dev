# Pledges

Now we will look at [`pledges`](../verify/pledge.md). Pledges are used for functions that return mutable references into some datastructure.
With a pledge you can explain to Prusti how the original object gets affected by changes to the returned reference.
We will demonstrate by implementing a function that gives you a mutable reference to the first element in the list.

## Implementing `peek_mut`

The `peek_mut` will return a mutable reference of type `T`, so the precondition of the list requires it to be non-empty.
As a first postcondition, we want to ensure that the `result` of `peek_mut` points to the first element of the list.

In the code, we need to get a mutable reference to the type inside the `Link = Option<Box<Node<T>>>`. This requires the use of the type `Option<&mut T>`, which is a structure containing a reference, so it is not yet supported by Prusti. To still be able to verify `peek_mut`, we mark it as `trusted` for now:

<!-- TODO: link capabilities/limitations chapter (refs in structs) -->

```rust,noplaypen
{{#rustdoc_include ../../../../prusti-tests/tests/verify/fail/user-guide/peek_mut_pledges.rs:peek_mut_code}}
```

Note that `peek_mut` cannot be `#[pure]`, since it returns a mutable reference.

## Writing a test for our specification

Let's write a test to see if our specification works:
- Create a list with two elements: [16, 8]
- Get a mutable reference to the first element (16)
- Change the first element to 5
- Check if the list still has the expected properties after `first` gets dropped
  - Is the length 2?
  - Is the first element 5?
  - Is the second element 8?

```rust,noplaypen
{{#rustdoc_include ../../../../prusti-tests/tests/verify/fail/user-guide/peek_mut_pledges.rs:test_peek_mut}}
```

But this fails, Prusti cannot verify any of our last three `prusti_assert` statements. This is where pledges come in. We have to tell Prusti how the `result` affects the original list. Without this, Prusti assumes that changes to the reference can change every property of the original list, so nothing can be known about it after the reference gets dropped.

## Writing the pledge

The pledge is written using an annotation, like `ensures` and `requires`, but with the keyword `after_expiry`.
Inside we have all the conditions that hold after the returned reference gets dropped:

```rust,noplaypen
{{#rustdoc_include ../../../../prusti-tests/tests/verify/pass/user-guide/peek_mut_pledges.rs:pledge}}
```

We have three properties here:
1. The list will have the same length afterwards.
2. Any element of the list with index `1..list.len()` will not be changed.
3. The element at the head of the list is the value that was assigned to the returned reference. This is denoted with the `before_expiry` function.

With these three properties specified, our test verifies successfully!

## Assert on expiry

Like `after_expiry`, there is also `assert_on_expiry`. It is used to check for conditions that have to be true when the returned reference expires, usually in order to uphold some type invariant.

As an example, we could use this to make sure that our list of `i32` can only contain elements between 0 and 16.
Given that this invariant held before the reference was given out, it will hold again only if the element, potentially changed by the caller, is still in the correct range:

```rust,noplaypen,ignore
{{#rustdoc_include ../../../../prusti-tests/tests/verify/pass/user-guide/assert_on_expiry.rs:assert_on_expiry}}
```
The syntax here is `#[assert_on_expiry(condition, pledge)]`.
This means that `condition` is checked at the caller side *before* (or "when") the reference expires, and `pledge` must hold *after* the reference expires.

Note that for any assertion `A`, `after_expiry(A)` is equivalent to `assert_on_expiry(true, A)`.

## Full Code

```rust,noplaypen
// Expand to see full code up to this chapter
{{#rustdoc_include ../../../../prusti-tests/tests/verify/pass/user-guide/peek_mut_pledges.rs:nothing}}
```
