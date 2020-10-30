# Trait contract refinement

> **NOT YET SUPPORTED:** This feature is not yet supported in the new version of Prusti.

In some cases, marker traits simply modify the behavior of methods in their super-traits. For instance consider the `PartialEq<T>` and `Eq` traits. In order to consider this additional behavior for verification, traits support contract refinement on trait level:

```rust
pub trait PartialEq<Rhs: ?Sized = Self> {
    #[ensures(/* partial equivalence formulas */)]
    fn eq(&self, other: &Rhs) -> bool;
}

#[refine_ensures(PartialEq::eq = "self.eq(&self)")]
pub trait Eq: PartialEq<Self> {}
```

Thus, any client implementing `Eq` on a custom type can take advantage of the additional semantics of the total equivalence. Similarly `#[refine_requires]` can be used to refine the precondition of a super-trait.

> Such trait refinement is not scoped. Therefore, considering the previous example, implementing `Eq` on a type implies that the total equivalence contract is always considered on the type, irrespective of whether `Eq` is in scope or not.
