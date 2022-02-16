# Getting Started

Our first goal is to implement and verify a simple singly-linked stack that stores
32 bit integers *without* relying on existing data structures 
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

## Stack Layout

Our naïve singly-linked stack is composed of a public structure `List` storing 
the head of the list, an enum `Link` representing either an empty list or a heap-allocated
Node storing the payload—an integer—and the link to the next node:

```rust,noplaypen
{{#include tour-src/03-chapter-2-1.rs:1:13}}
// Prusti: VERIFIES
```

This design avoid making both `Link` and `Node` public.
Moreover, it benefits from the Rust compiler's [null-pointer optimization](https://rust-lang.github.io/unsafe-code-guidelines/layout/enums.html#discriminant-elision-on-option-like-enums)
and makes sure that all list elements are uniformly allocated on the heap.

## Absence of Runtime Errors

Prusti automatically checks that no statement or macro that causes
an explicit runtime error, such as
[`panic`](https://doc.rust-lang.org/std/macro.panic.html),
[`unreachable`](https://doc.rust-lang.org/std/macro.unreachable.html),
[`unimplemented`](https://doc.rust-lang.org/std/macro.unimplemented.html), or
possibly a failing [assertion](https://doc.rust-lang.org/std/macro.assert.html),
is reachable.

For example, the following test function creates a node with no successor and panics
if the node's payload is greater than 23:

```rust,noplaypen
#pub struct List {
#    head: Link,
#}
#
#enum Link {
#    Empty,
#    More(Box<Node>),
#}
#
#struct Node {
#    elem: i32,
#    next: Link,
#}
#
{{#include tour-src/03-chapter-2-1.rs:15:24}}
// Prusti: VERIFIES
```
Prusti successfully verifies the above function 
because it can statically guarantee that `test.elem <= 23` holds 
whenever execution reaches the `if` statement.

This is not the case for the following function in which the test node is initialized
with an arbitrary integer:
```rust,noplaypen
#pub struct List {
#    head: Link,
#}
#
#enum Link {
#    Empty,
#    More(Box<Node>),
#}
#
#struct Node {
#    elem: i32,
#    next: Link,
#}
#
#fn main() {}
#
{{#include tour-src/03-fail.rs:26:35}}
// Prusti: FAILS
```

Prusti reports errors in the same fashion as the Rust compiler (although with the prefix
`Prusti: verification error`). For example, the error produced for the above function
is:

```
error: [Prusti: verification error] panic!(..) statement might be reachable
  --> 03-fail.rs:33:9
   |
33 |         panic!()
   |         ^^^^^^^^
   |
   = note: this error originates in a macro (in Nightly builds, run with -Z macro-backtrace for more info)
Verification failed
```
