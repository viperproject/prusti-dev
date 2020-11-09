# External specifications

Since the Rust standard library and external libraries do not specify contracts for their functions, Prusti allows specifying the contract for functions separately from where they are implemented. Such a specification looks like a regular `impl`, with the exception that there are no bodies in the implementation functions, and that the `impl` has an `#[extern_spec]` attribute.

The standard library type `std::option::Option` could be specified as follows:

```rust
extern crate prusti_contracts;
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

Module functions can be specified using a nested `mod` syntax:

```rust
extern crate prusti_contracts;
use prusti_contracts::*;

#[extern_spec]
mod std {
    mod mem {
        use prusti_contracts::*;

        #[ensures(*a == old(*b) && *b == old(*a))]
        pub fn swap(a: &mut i32, b: &mut i32);
        // pub fn swap<T: std::cmp::PartialEq + Copy>(a: &mut T, b: &mut T);
    }
}
```

There are currently issues with external specifications combined with generics, so the function `swap` above is specified for `i32` arguments only.
