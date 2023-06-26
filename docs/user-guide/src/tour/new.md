# New 

> **Recommended reading:** 
> [2.2: New](https://rust-unofficial.github.io/too-many-lists/first-new.html), 
> [2.3: Ownership 101](https://rust-unofficial.github.io/too-many-lists/first-ownership.html)
> 
> How to associate code with a type through `impl` blocks; 
> writing simple static functions;
> Rust's ownership system.

## Implementing `new`

We first provide a static function to create empty lists:

```rust,noplaypen
{{#rustdoc_include ../../../../prusti-tests/tests/verify/pass/user-guide/impl_new.rs:impl_new}}
// Prusti: VERIFIES
```

## A first specification

What would be a sensible first specification for `new()`?
We could attempt to verify the list returned by `new()` is always empty.
In other words, the length of the returned list is always zero.
To express this property, we first implement a length method for lists which
itself calls an auxiliary length method implemented for `Link`.
For simplicity, we will not actually compute the length of a `Link` yet.
Rather, we will just always return 0. The return type for the `len` functions is [`usize`](https://doc.rust-lang.org/std/primitive.usize.html), which is a pointer-sized unsigned integer (e.g., 64 bits on a 64-bit computer). `usize` is also used in the [`Vec::len`](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.len) function in the standard library.

```rust,noplaypen
{{#rustdoc_include ../../../../prusti-tests/tests/verify/fail/user-guide/impl_new_spec_1.rs:first_spec_1}}
// Prusti: VERIFIES
```

Now that we have implemented a method for computing the length of a list, we can
write our first specification for `new()`: the returned list should always have length
zero.
That is, we attach the [postcondition](../verify/prepost.md)
`result.len() == 0` to the function `new()`. The special variable [`result`](../syntax.md#result-variable) is used in Prusti specifications to refer to the value that is returned by a function:

```rust,noplaypen
{{#rustdoc_include ../../../../prusti-tests/tests/verify/fail/user-guide/impl_new_spec_1.rs:first_spec_2}}
```

Unfortunately, Prusti—or rather, the Rust compiler—will complain about
the postcondition:

```plain
error: cannot find attribute `ensures` in this scope
  --> list.rs:39:7
   |
39 |     #[ensures(result.len() == 0)]    
   |       ^^^^^^^
```

Prusti's specifications consist of Rust
[macros and attributes](https://doc.rust-lang.org/reference/procedural-macros.html)
that are defined in a separate crate called `prusti-contracts`. To see how to add this crate to your project, see the [Setup chapter](setup.md).
Before we can use these specifications, we need to make the path to these
macros and attributes visible:

```rust,noplaypen
{{#rustdoc_include ../../../../prusti-tests/tests/verify/fail/user-guide/impl_new_spec_2.rs:import_prusti}}
```

Declaring that we use the `prusti_contracts` module removes the compiler error but
leads to a new error. This time it is an error raised by Prusti:

```markdown
error: [Prusti: invalid specification] use of impure function "List::len" in pure code is not allowed
  --> list.rs:34:15
   |
34 |     #[ensures(result.len() == 0)]    
   | 
```

Prusti complains about our use of the method `len()` in a postcondition because the
[specification syntax](../syntax.md) only admits calling so-called
[pure functions](../verify/pure.md), that is, functions that are deterministic,
have no side effects, and always terminate.

While our implementation of `len()` clearly satisfies all of the above properties,
Prusti requires us to explicitly mark a function with the `#[pure]` attribute
before it considers a function pure.
After adding the `#[pure]` attribute to our `List::len()` method, it is allowed to
appear in Prusti specifications:

```rust,noplaypen
{{#rustdoc_include ../../../../prusti-tests/tests/verify/fail/user-guide/impl_new_spec_3.rs:pure_annotation}}
```

However, Prusti still won't verify! It produces the same error but now it refers
to the *body* of `len()`:

```plain
error: [Prusti: invalid specification] use of impure function "Link::len" in pure code is not allowed
  --> list.rs:30:9
   |
30 |         self.head.len() // (5)
   |         ^^^^
```

Whenever we add the attribute `#[pure]` to a function, Prusti will check whether that
function is indeed deterministic and side-effect free
(notice that termination is *not* checked); otherwise, it complains.
In this case, Prusti complains because we call an impure function,
namely `Link::len()`, within the body of the pure function `List::len()`.

<!-- TODO: link capabilities/limitations chapter (termination) -->

To fix this issue, it suffices to mark `Link::len()` as pure as well.

```rust,noplaypen
{{#rustdoc_include ../../../../prusti-tests/tests/verify/pass/user-guide/impl_new_spec_fixed.rs:pure_annotation}}
// Prusti: VERIFIES
```

```plain
$ cargo prusti
// ...
Successful verification of 4 items
```

Prusti now manages to verify that `new()` always returns
a list for which the method `len()` returns 0. (notice
this is hardly surprising since `len()` ultimately always returns 0.)

## Proper implementation of `len`

We will now properly implement `len()`, and while we're at it, `is_empty()` for `Link`. Both of them are pure functions, so we will add the `#[pure]` annotation. Both functions can be called without any restrictions, so they have the default postcondition `#[requires(true)]`, which we don't have to add manually. We also don't need to add any additional postconditions, since the body of pure functions is considered to be part of their contract.

```rust,noplaypen
{{#rustdoc_include ../../../../prusti-tests/tests/verify/pass/user-guide/impl_new_full_code.rs:implementation}}
```

Here we use the [`matches!` macro](https://doc.rust-lang.org/std/macro.matches.html) in `is_empty`, which is true if and only if the first argument matches the pattern in the second argument.

We can now check if the specification is working, by writing a function that panics if the specification is wrong:
```rust,noplaypen
{{#rustdoc_include ../../../../prusti-tests/tests/verify/pass/user-guide/impl_new_full_code.rs:test_len}}
```

The last line asserts that the `is_empty` function only returns `true` if the `len` function returns `0`.
And Prusti can verify it! Now we know that this assert statement holds for any `link` that is passed to the `test_len` function.
Note that we wrote this function only for demonstration purposes—the contract is checked even without the `test_len` function. We will consider the relationship between testing and static verification further in the [Testing chapter](testing.md).

### Overflow checks

Here you can also see why we disabled overflow checking for this tutorial. If you remove the `check_overflows = false` flag in the `Prusti.toml` file, and then try to verify the crate again, you will get an error:
```plain
[Prusti: verification error] assertion might fail with "attempt to add with overflow"
    Link::More(node) => 1 + node.next.len(),
                        ^^^^^^^^^^^^^^^^^^^
```
This overflow could happen, if you call `len` on a list with more than `usize::MAX` elements. To prevent this verification error, we would have to constrain the maximum size of a `List`, which is beyond this tutorial. 

## Full code listing

Before we continue, we provide the full code implemented in this chapter.
It should successfully verify with Prusti and we will further extend it throughout
the next chapters.

```rust,noplaypen
// Expand to see full code up to this chapter
{{#rustdoc_include ../../../../prusti-tests/tests/verify/pass/user-guide/impl_new_full_code.rs:nothing}}
```
