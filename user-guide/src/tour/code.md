# Guided Tour

> **Disclaimer:** All code shown in this tutorial has been tested with 
> [Prusti v-2021-06-11-14-13](https://github.com/viperproject/prusti-dev/tree/v-2021-06-11-1413).

In this chapter, we demonstrate Prusti's capabilities.
As a running example, we roughly follow the first chapters of the Rust tutorial
[Learn Rust with Entirely Too Many Linked Lists](https://rust-unofficial.github.io/too-many-lists/).
Linked lists turn out to be sufficiently awful that their implementation and verification
covers most of Rust's and Prusti's essential concepts.
While the above tutorial explains in detail how linked lists are implemented in Rust,
we additionally aim to verify that the implemented list operations are functionally
correct.

While we assume basic familiarity with Rust, it is possible to learn both
Rust and Prusti at the same time by reading this tour and the 
[Rust tutorial](https://rust-unofficial.github.io/too-many-lists/)
that inspired it in an interleaved fashion.
We will provide pointers to the Rust tutorial for beginners to catch up where appropriate.

Throughout this tour, we will cover the following Prusti concepts:

- How Prusti reports errors and integrates into the development process
- Runtime errors detected by Prusti
- Writing function-modular specifications 
- Using *pure* functions in specifications
- Writing loop invariants 
- Using *trusted wrappers* to deal with library code
- Basic troubleshooting


The individual chapters are found in the sidebar, which may be collapsed on mobile
devices.
As a quick reference, the main steps of this tour and the involved Prusti features
are as follows:

1. [Getting Started](getting-started.md): Simple runtime errors catched by Prusti
2. [New](new.md): Postconditions, pure functions
3. [Push](push.md): Preconditions, trusted functions, old expressions, quantifiers
4. [Pop](pop.md): Exercise with similar concepts as for push
5. [Testing](testing.md): More runtime errors catched by Prusti
6. [A Bad Stack](bad-stack.md): Wrap-up of the second chapter of
   [Learn Rust with Entirely Too Many Linked Lists](https://rust-unofficial.github.io/too-many-lists/).
7. [Options](options.md): Verification with option types
7. [Generics](generics.md): Prusti and generics
8. [Peek](peek.md): Exercise
9. [Final Code](final.md): Final code with solution of exercise
10. [Pledges](pledges.md): Bonus demonstrating Prusti's pledges


## Getting started

Our starting 
That is, we implement a simple singly-linked stack and additionally verify
that the involved operations are functionally correct.


```bash
$ prusti-rustc --edition=2018 path/to/file.rs
```

```rust,noplaypen
#fn max(a: i32, b: i32) -> i32 {
    if a > b {
        a
    } else {
        b
    }
#}
```

```rust,noplaypen
{{#include tour-src/01-chapter-2-1.rs:1:}}
```

```rust,noplaypen
{{#include tour-src/02-chapter-2-1.rs:1:}}
```

```rust,noplaypen
{{#include tour-src/03-chapter-2-1.rs:1:}}
```

```rust,noplaypen
{{#include tour-src/04-chapter-2-2.rs:1:}}
```

```rust,noplaypen
{{#include tour-src/05-chapter-2-3.rs:1:}}
```

```rust,noplaypen
{{#include tour-src/06-chapter-2-4.rs:1:}}
```

```rust,noplaypen
{{#include tour-src/07-chapter-2-4.rs:1:}}
```

```rust,noplaypen
{{#include tour-src/08-chapter-2-4.rs:1:}}
```

```rust,noplaypen
{{#include tour-src/09-chapter-2-4.rs:1:}}
```

```rust,noplaypen
{{#include tour-src/10-chapter-2-5.rs:1:}}
```

```rust,noplaypen
{{#include tour-src/11-chapter-2-5.rs:1:}}
```

```rust,noplaypen
{{#include tour-src/12-chapter-2-6.rs:1:}}
```

```rust,noplaypen
{{#include tour-src/13-too-many-lists-final.rs:1:}}
```

