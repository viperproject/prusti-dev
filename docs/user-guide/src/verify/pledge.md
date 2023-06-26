# Pledges

Pledges are a construct that can be used to specify the behaviour of functions that reborrow. For example, pledges should be used for modelling an assignment to a vector element because, in Rust, `v[i] = 4` is not a method call `v.store(i, 4)` but rather `let tmp = v.get_mut(i); *tmp = 4`, where `get_mut` is a method that reborrows the `v` receiver to return a reference to a particular element.

As a full example, a wrapper around Rust `Vec<i32>` could be implemented as follows:

```rust,noplaypen,ignore
use prusti_contracts::*;

pub struct VecWrapperI32 {
    v: Vec<i32>
}

impl VecWrapperI32 {
    #[trusted]
    #[pure]
    #[ensures(result >= 0)]
    pub fn len(&self) -> usize {
        self.v.len()
    }

    /// A ghost function for specifying values stored in the vector.
    #[trusted]
    #[pure]
    #[requires(0 <= index && index < self.len())]
    pub fn lookup(&self, index: usize) -> i32 {
        self.v[index]
    }

    #[trusted]
    #[requires(0 <= index && index < self.len())]
    #[ensures(*result == old(self.lookup(index)))]
    #[after_expiry(
        self.len() == old(self.len()) &&
        self.lookup(index) == before_expiry(*result) &&
        forall(
            |i: usize| (0 <= i && i < self.len() && i != index) ==>
            self.lookup(i) == old(self.lookup(i))
        )
    )]
    pub fn index_mut(&mut self, index: usize) -> &mut i32 {
        self.v.get_mut(index).unwrap()
    }
}
```

The syntax for a pledge is `#[after_expiry(reference => condition)]` where
`reference` is the reborrowing reference (defaults to `result`, which is
currently the only thing one can write until we have support for
reference fields) and `condition` is a [Prusti specification](../syntax.md) that specifies how the borrowed data
structure will look once the borrow expires. To refer in the condition to the state that
a memory location pointed at by the reference has just before expiring,
use `before_expiry(*reference)`.

## Run assertions when reference expires

In some cases, a condition must be checked at the point of expiry, like for example a type invariant.
The syntax for this is `#[assert_on_expiry(condition, invariant)]`.
This means that the `invariant` holds, given that `condition` is true when the reference expires.

Note that for any assertion `A`, `after_expiry(A)` is equivalent to `assert_on_expiry(true, A)`.
