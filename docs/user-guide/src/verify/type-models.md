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

> **Caution**
>
> As of yet, iterators are not fully supported in Prusti.
> The example above is a draft and is meant as a possible real-world usage of `#[model]` in the near future.

## Remarks
* A model needs to be copyable, i.e. all fields need to be `Copy`.
* When the modelled type has no fields, a warning will be emmitted. Using `.model()` on such types can
  lead to unsound verification results. See below for an example.
* The model is only to be used in specifications (pre- and postconditions of functions or methods)
  and never in code which will be executed. Using `.model()` in non-spec code will cause a Prusti error.
* Models can currently not be generic, i.e. creating a model for `Vec<T>` is not possible. It is however
  possible to model concrete generic types, i.e. `Vec<i32>` and `Vec<u32>`.

### Modelled types should have fields
Using models on types without fields can have unexpected verification behavior as shown in the code snippet below:
```rust
struct A; // no fields
#[model] 
struct A { val: i32 }
#[trusted]
#[ensures( result.model().val == with_model_val )]
fn create_a(with_model_val: i32) -> A { A {} }

fn main() {
  let a1 = create_a(42);
  let a2 = create_a(43);
  // Can prove: a1.model().val == x for any x
  // Can prove: a2.model().val == x for any x
}
```
The reason for this is due to the encoding of `A` in Viper. When encoding the `main` function, Prusti creates two
snapshots for `a1` and `a2`. Since `A` has no fields, any two snapshots of `A` will be considered equal 
and thereafter, their models too. 
When inhaling the two postconditions for the call to `create_a` in `main`, Viper thus basically assumes 
that the field `val` for the *same* model is `42` and `43`, a contradiction.