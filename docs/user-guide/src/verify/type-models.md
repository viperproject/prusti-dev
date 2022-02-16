# Type Models

Some structs, mostly non-local structs from other crates, contain non-public code which are essential for verification.
An example is the `std::slice::Iter` struct from the standard library.
We would like to provide a specification for the `Iterator` implementation of `Iter<'_, i32>`:

```rust
impl Iterator<'a, T> for std::slice::Iter<'a, i32>{
    // ??? spec involving Iter ???
    fn next(&mut self) -> Option<&'a T>;
}
```

There is not really a way to provide a specification for this implementation, because `Iter`'s fields do not allow a [straightforward specification](https://doc.rust-lang.org/src/core/slice/iter.rs.html#65-71).

We can instead provide a model for `Iter` in the following way, using the `#[model]` macro:
```rust
use std::slice::Iter;
#[model]
struct Iter<'a, i32> {
     position: usize,
     len: usize,
}
```
This allows an instance of `Iter<'_, i32>` to be modelled by the two fields `position` and `len`.

The model can then be used in specifications:
```rust
#[ensures( result.model().position == 0 )]
#[ensures( result.model().len == slice.len() )]
#[trusted]
fn create_iter(slice: &[i32]) -> std::slice::Iter<'_, i32> {
   slice.iter()
}

#[extern_spec]
impl Iterator for std::slice::Iter<'a, i32>{
    type Item = i32;

    #[ensures( self.model().data.len == old(self.model().data.len)) )]
    #[ensures( old(self.model().pos) < self.model().data.len ==> 
                            ( result.is_some() && 
                              result.unwrap() == self.model().data[old(self.model().pos)]))
    ]
    // ... more ...
    fn next(&mut self) -> Option<&'a T>;
}
```

## Remarks
* A model needs to be copyable, i.e. all fields need to be `Copy`.
* The model is only to be used in specifications (pre- and postconditions of functions or methods)
  and never in code which will be executed. Using `.model()` in non-spec code will cause a Prusti error.
* Models can currently not be generic, i.e. creating a model for `Vec<T>` is not possible. It is however
  possible to model concrete generic types, i.e. `Vec<i32>` and `Vec<u32>`.

> **Caution**
>
> As of yet, iterators are not fully supported in Prusti.
> The example above is a draft and is meant as a possible real-world usage of `#[model]` in the near future.