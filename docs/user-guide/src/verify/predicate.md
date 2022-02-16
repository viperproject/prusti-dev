# Predicates

Predicates are similar to [pure functions](pure.md) in that they are deterministic and side-effect free and used in specifications.

They are more powerful than pure functions: inside predicate bodies the full [Prusti specification syntax](../syntax.md) is allowed. However, they are not usable in regular Rust code, as there are no direct Rust equivalents for specification constructs like [quantifiers](../syntax.md#quantifiers) or [implications](../syntax.md#implications). Instead, predicates can only be called from within specifications.

Predicates are declared using the `predicate!` macro on a function:

```rust
predicate! {
    fn all_zeroes(a: &MyArray) -> bool {
        forall(|i: usize|
            (0 <= i && i < a.len() ==> a.lookup(i) == 0))
    }
}
```

Within specifications, predicates can be called just like pure functions:

```rust
#[ensures(all_zeros(a))]
fn zero(a: &mut MyArray) { ... }
```

The `predicate!` macro is incompatible with other Prusti specifications, i.e. a predicate function cannot have pre- or postconditions. The body of a predicate must be provided, so it cannot be [`#[trusted]`](trusted.md). Predicates are always considered pure.
