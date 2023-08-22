# Type-Conditional Spec Refinement

When specifying trait methods or generic functions, there is often a special case that allows for more complete specification. In these cases, you can attach a type-conditional spec refinement attribute to the function in question, spelled e.g. `#[refine_spec(where T: A + B, U: C, [requires(true), pure])]`

For example, one could use this to specify a function like `core::mem::size_of` by defining a trait for types whose size we'd like to specify:

```rust,noplaypen,ignore
#[pure]
#[refine_spec(where T: KnownSize, [
    ensures(result == T::size()),
])]
fn size_of<T>() -> usize;

pub trait KnownSize {
    #[pure]
    fn size() -> usize;
}
```

> Note that the involved functions are marked as `pure`, allowing them to be used within specifications. This is another common use case, because functions can only be `pure` if their parameters and result are `Copy`, so it is often useful to specify something like `#[refine_spec(where T: Copy, [pure])]`.

There are some marker traits which simply modify the behavior of methods in their super-traits. For instance, consider the `PartialEq<T>` and `Eq` traits. In order to consider this additional behavior for verification, we can refine the contract of `PartialEq::eq` when the type is known to be marked `Eq`:

```rust,noplaypen,ignore
pub trait PartialEq<Rhs: ?Sized = Self> {
    #[refine_spec(where Self: Eq, [
        ensures(self == self), // reflexive
        // we could write more specs here
    ])]
    #[ensures(/* partial equivalence formulas */)]
    fn eq(&self, other: &Rhs) -> bool;
}
```

Thus, any client implementing `Eq` on a custom type can take advantage of the additional semantics of the total equivalence.
