# Guided Tour

> **Disclaimer:** All code shown in this tutorial has been tested with 
> [Prusti v-2021-06-11-14-13](https://github.com/viperproject/prusti-dev/tree/v-2021-06-11-1413).
>
> Unless stated otherwise, all code listings should be put in their own file 
> and can be verified with 
> [Prusti assistant](https://marketplace.visualstudio.com/items?itemName=viper-admin.prusti-assistant).

In this chapter, we demonstrate Prusti's capabilities.
As a running example, we roughly follow the first chapters of the Rust tutorial
[Learn Rust with Entirely Too Many Linked Lists](https://rust-unofficial.github.io/too-many-lists/).
Linked lists turn out to be sufficiently complex that their implementation and verification
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

1. [Getting Started](getting-started.md): Simple runtime errors caught by Prusti
2. [New](new.md): Postconditions, pure functions
3. [Push](push.md): Preconditions, trusted functions, old expressions, quantifiers
4. [Pop](pop.md): Exercise with similar concepts as for push
5. [Testing](testing.md): More runtime errors caught by Prusti
6. [A Bad Stack](bad-stack.md): Wrap-up of the second chapter of
   [Learn Rust with Entirely Too Many Linked Lists](https://rust-unofficial.github.io/too-many-lists/).
7. [Options](options.md): Verification with option types
7. [Generics](generics.md): Prusti and generics
8. [Peek](peek.md): Exercise
9. [Final Code](final.md): Final code with solution of exercise
10. [Pledges](pledges.md): Bonus demonstrating Prusti's pledges
