# External specifications

Since the Rust standard library and external libraries do not specify contracts for their functions, Prusti allows specifying the contract for functions separately from where they are implemented. Such a specification looks like a regular `impl`, with the exception that there are no bodies in the implementation functions, and that the `impl` has an `#[extern_spec]` attribute.

The standard library type `std::option::Option` could be specified as follows:

```rust,noplaypen,ignore
use prusti_contracts::*;

#[extern_spec]
impl<T> std::option::Option<T> {
    #[pure]
    #[ensures(matches!(*self, Some(_)) == result)]
    pub fn is_some(&self) -> bool;

    #[pure]
    #[ensures(self.is_some() == !result)]
    pub fn is_none(&self) -> bool;

    #[requires(self.is_some())]
    pub fn unwrap(self) -> T;

    // ...
}
```

Any function in an external specification is implicitly [trusted](trusted.md) (as if marked with `#[trusted]`). It is possible to specify multiple `#[extern_spec]` implementations for the same type, but it is an error to externally specify the same function multiple times.

The `extern_spec` attribute accepts an optional argument to provide the module path to the function being specified. For example, to specify `std::mem::swap`, the argument is `std::mem`:

```rust,noplaypen,ignore
use prusti_contracts::*;

#[extern_spec(std::mem)]
#[ensures(*a === old(snap(b)) && *b === old(snap(a)))]
fn swap<T>(a: &mut T, b: &mut T);
```
