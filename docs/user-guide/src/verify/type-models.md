# Type Models

Some structs, mostly non-local structs from other crates, contain non-public code which are essential for verification.
To provide a specification for such structs, you can add model fields to be used in specifications. To introduce a type
model for a struct, simply annotate it with the `#[model]` macro and declare the to-be-modelled fields inside the
struct:

```rust,noplaypen,ignore
#[model]
struct SomeStruct {
    some_i32: i32,
    // ... more fields
}
```

You then can use the model of `SomeStruct` inside specifications via the `.model()` function:

```rust,noplaypen,ignore
#[requires(some_struct.model().some_i32 == 42)]
fn some_method(some_struct: &SomeStruct) {
    // ...
}
```

A model cannot be used outside of specification code, that is the following code will emit an error in Prusti and panic
when executed:

```rust,noplaypen,ignore
fn some_client(some_struct: &mut SomeStruct) {
    some_struct.model().some_i32 = 42;
}
```

This means that a model cannot be instantiated or directly manipulated with runtime code. Instead, the _source_ of a
model is always a [trusted function](trusted.md) or an [external specification](external.md).

## Further remarks

* A model needs to be copyable, i.e. all fields need to be `Copy`. That also applies to type parameters where you need
  to add the `Copy` trait as a bound.
* When the modelled type has no fields, a warning will be emmitted. Using `.model()` on such types can lead to unsound
  verification results. See below for an example.

### Modelled types should have fields

Using models on types without fields can have unexpected verification behavior as shown in the code snippet below:

```rust,noplaypen,ignore
struct A;

// no fields
#[model]
struct A {
    val: i32
}

#[trusted]
#[ensures(result.model().val == with_model_val)]
fn create_a(with_model_val: i32) -> A { A {} }

fn main() {
    let a1 = create_a(42);
    let a2 = create_a(43);
    // Can prove: a1.model().val == x for any x
    // Can prove: a2.model().val == x for any x
}
```

The reason for this is due to the encoding of `A` in Viper. When encoding the `main` function, Prusti creates two
snapshots for `a1` and `a2`. Since `A` has no fields, any two snapshots of `A` will be considered equal and thereafter,
their models too. When inhaling the two postconditions for the call to `create_a` in `main` Viper thus assumes that the
field `val` for the *same* model is `42` and `43`, a contradiction.

## Example: `std::iter::Iter`

> **Caution**
>
> As of yet, iterators are not fully supported in Prusti.
> This example is a draft and is meant as a possible real-world usage of `#[model]` in the near future.

An example where a type model comes in handy is the `std::slice::Iter` struct from the standard library. We would like
to provide a specification for the `Iterator`:

```rust,noplaypen,ignore
impl<T> Iterator<'a, T> for std::slice::Iter<'a, T> {
    // ??? spec involving Iter ??? 
    fn next(&mut self) -> Option<&'a T>;
}
```

There is not really a way to provide a specification for this implementation, because `Iter`'s fields do not allow
a [straightforward specification](https://doc.rust-lang.org/src/core/slice/iter.rs.html#65-71).

We can instead provide a model for `Iter` in the following way, using the `#[model]` macro:

```rust,noplaypen,ignore
use std::slice::Iter;

#[model]
struct Iter<'a, #[generic] T: Copy> {
    position: usize,
    len: usize,
    data: GhostSeq<T> // Note: Assuming this is defined somewhere
}
```

This allows an instance of `Iter<'_, T>` to be modelled by the fields `position`, `len` and `data`.

The model can then be used in specifications:

```rust,noplaypen,ignore
#[ensures(result.model().position == 0)]
#[ensures(result.model().len == slice.len())]
#[trusted]
fn create_iter<T>(slice: &[T]) -> std::slice::Iter<'_, T> {
    slice.iter()
}

#[extern_spec]
impl<T> Iterator for std::slice::Iter<'a, T> {
    type Item = T;

    # [ensures( self .model().data.len == old( self .model().data.len)) )]
    #[ensures(old(self.model().pos) < self.model().data.len == >
    ( result.is_some() &&
    result.unwrap() == self.model().data.lookup(old(self.model().pos))))
    ]
    // ... more ...
    fn next(&mut self) -> Option<&'a T>;
}
```