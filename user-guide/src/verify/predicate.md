# Predicates

Predicates are somewhat like pure functions in that they are
deterministic and side-effect free and used in specifications.

They are more powerful than pure functions: inside predicates the full
[Prusti specification syntax](../syntax.md) is allowed. In exchange,
they are not usable in regular Rust code, as there are no direct Rust
equivalents for specification constructs like
[quantifiers](../syntax.md#quantifiers) or
[implications](../syntax.md#implications).

```rust
#[predicate]
fn all_zeroes(a: MyArray) -> bool {
	forall(|i: usize|
		(0 <= i && i < a.len() ==> a.lookup(i) == 0))
}
```

Predicates are incompatible with other types of Prusti specifications,
i.e. they don't have pre- or postconditions, and as their function
bodies aren't Rust but Prusti syntax, it doesn't make sense to declare
them `#[pure]` or `#[trusted]` (or, in some sense, they are
automatically).
