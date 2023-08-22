# Verification Features

Even if no specifications are provided, Prusti is capable of verifying a few basic properties about the supplied Rust code.
These properties include:

- [Absence of panics](panic.md)
- [Overflow checks](overflow.md)

More intricate properties require users to write suitable [specifications](../syntax.md).
The following features are either currently supported or planned to be supported in Prusti:

- [Pre- and postconditions](prepost.md)
- [Assertions, refutations and assumptions](assert_refute_assume.md)
- [Trusted functions](trusted.md)
- [Pure functions](pure.md)
- [Predicates](predicate.md)
- [External specifications](external.md)
- [Loop body invariants](loop.md)
- [Pledges](pledge.md)
- [Type-conditional spec refinements](type_cond_spec.md)
- [Closures](closure.md)
- [Specification entailments](spec_ent.md)
- [Type models](type-models.md)
- [Conditional compilation](prusti-feature.md)

By default, Prusti only checks absence of panics.
Moreover, Prusti verifies *partial* correctness. That is, it only verifies that *terminating* program executions meet the supplied specification.
