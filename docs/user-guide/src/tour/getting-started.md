# Getting Started

Our first goal is to implement and verify a simple singly-linked stack that stores
32-bit integers *without* relying on existing data structures 
provided by Rust's standard library.

For readers that are unfamiliar with Rust, this is a good time to additionally
read the introduction of the accompanying Rust tutorial 
[Learn Rust With Entirely Too Many Linked Lists](https://rust-unofficial.github.io/too-many-lists/index.html),
which explains the Rust features covered by the tutorial and how to set up a 
new project with Cargo.
 
From now on, we will simply provide links to the relevant parts of the
Rust tutorial together with a brief summary. 
For example, reading up on possible data layouts for lists might be useful for beginners:

> **Recommended reading:** 
> [2.1: Basic Data Layout](https://rust-unofficial.github.io/too-many-lists/first-layout.html)
>
> Discusses potential pitfalls and errors when setting up a singly-linked data structure in Rust.

## Stack layout

Our naïve singly-linked stack is composed of a public structure `List` storing 
the head of the list, an enum `Link` representing either an empty list or a heap-allocated
Node storing the payload—an integer—and the link to the next node:

```rust,noplaypen
{{#rustdoc_include ../../../../prusti-tests/tests/verify/pass/user-guide/getting_started_working.rs:types}}
// Prusti: VERIFIES
```

As explained in the chapter [2.1: Basic Data Layout](https://rust-unofficial.github.io/too-many-lists/first-layout.html), this design avoids making both `Link` and `Node` public.
Moreover, it benefits from the Rust compiler's [null-pointer optimization](https://rust-lang.github.io/unsafe-code-guidelines/layout/enums.html#discriminant-elision-on-option-like-enums)
and makes sure that all list elements are uniformly allocated on the heap.

## Absence of runtime errors

Prusti automatically checks that no statement or macro that causes
an explicit runtime error, such as
[`panic!`](https://doc.rust-lang.org/std/macro.panic.html),
[`unreachable!`](https://doc.rust-lang.org/std/macro.unreachable.html),
[`unimplemented!`](https://doc.rust-lang.org/std/macro.unimplemented.html),
[`todo!`](https://doc.rust-lang.org/std/macro.todo.html), or
possibly a failing [assertion](https://doc.rust-lang.org/std/macro.assert.html),
is reachable. [Prusti assertions](../verify/assert_refute_assume.md) are also checked. These are like the normal `assert!` statements, but they can use the full Prusti specification syntax and will not result in any runtime checks or code when compiled normally.

For example, the following test function creates a node with no successor and panics
if the node's payload is greater than 23:

```rust,noplaypen
{{#rustdoc_include ../../../../prusti-tests/tests/verify/pass/user-guide/getting_started_working.rs:code}}
// Prusti: VERIFIES
```
Prusti successfully verifies the above function 
because it can statically guarantee that `test.elem <= 23` holds 
whenever execution reaches the `if` statement.

This is not the case for the following function in which the test node is initialized
with an arbitrary integer:
```rust,noplaypen
{{#rustdoc_include ../../../../prusti-tests/tests/verify/fail/user-guide/getting_started_failing.rs:failing_code}}
// Prusti: FAILS
```

Prusti reports errors in the same fashion as the Rust compiler (with the prefix
`Prusti: verification error`). For example, the error produced for the above function
is:

```plain
error: [Prusti: verification error] statement might panic
  --> getting_started_failing.rs:33:9
   |
33 |         panic!()
   |         ^^^^^^^^
```
