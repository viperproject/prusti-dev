# Heap-based type encoding

This encoding uses Viper [predicates](http://viper.ethz.ch/tutorial/?page=1&section=#predicates) and `Ref`s.

## Primitive types

A small number of Rust types have direct analogues in the Viper type system. However, because it is possible to reference local variables and arguments in Rust, all variables are encoded as `Ref`s, and specific fields are used to refer to the "primitive value" contained in those `Ref`s.

### `Bool`

`Bool` is encoded to Viper `Bool`.

```viper
field val_bool: Bool
predicate bool(self: Ref) {
  acc(self.val_bool, write)
}
```

### `i*`, `u*`, `char`

All Rust integers (`i8`, `i16`, `i32`, `i64`, `i128`, `isize`, `u8`, `u16`, `u32`, `u64`, `u128`, `usize`) and `char` are encoded to Viper `Int`.

```viper
field val_int: Int
predicate i32(self: Ref) {
  acc(self.val_int, write)
}
```

When the [`CHECK_OVERFLOWS`](../config/flags.md#check_overflows) flag is enabled, integer bounds are encoded with the type.

```viper
// with CHECK_OVERFLOWS
predicate i32(self: Ref) {
  acc(self.val_int, write) && -2147483648 <= self.val_int && self.val_int <= 2147483647
}
```

When the [`ENCODE_UNSIGNED_NUM_CONSTRAINT`](../config/flags.md#encode_unsigned_num_constraint) flag is enabled (even when `CHECK_OVERFLOWS` is not), non-negativity of unsigned integers is always encoded.

```viper
// with ENCODE_UNSIGNED_NUM_CONSTRAINT
predicate u32(self: Ref) {
  acc(self.val_int, write) && 0 <= self.val_int
}
```

## Composite types

There are no classes in Viper (every `Ref` instance has all fields), so non-primitive Rust types are encoded as predicates composed of multiple components.

### Tuples

Each component of a tuple is a field of type `Ref`, named `tuple_0`, `tuple_1`, etc. The type of each component is encoded recursively.

```viper
field tuple_0: Ref
field tuple_1: Ref
// ...

// for some types X and Y
predicate Tuple_X_Y(self: Ref) {
  acc(self.tuple_0, write) && X(self.tuple_0) &&
  acc(self.tuple_1, write) && Y(self.tuple_1)
}
```

### Structures

Structures are encoded similarly to tuples, except that fields names correspond to the names defined in the Rust type.

```rust,noplaypen
# type X = ();
# type Y = ();
# 
// for a Rust type, assuming types X and Y are defined
struct SomeStruct {
  a: X,
  b: Y,
}
```

```viper
field SomeStruct_a: Ref
field SomeStruct_b: Ref
predicate SomeStruct(self:Ref) {
  acc(self.SomeStruct_a, write) && X(self.SomeStruct_a) &&
  acc(self.SomeStruct_b, write) && Y(self.SomeStruct_b)
}
```

### Enumerations

Enumerations (ADTs) have values corresponding to one of their variants. Each variant can hold different types of data, so the Viper encoding contains implications of the form "if the variant of the value is X, the value contains the following fields". The variant index is encoded as the `discriminant` field.

```rust,noplaypen
# type X = ();
# 
// for a Rust type, assuming type X is defined
enum SomeEnum {
  Foo,
  Bar(X),
}
```

```viper
field discriminant: Int
field elt0: Ref
// ...

predicate SomeEnum(self: Ref) {
  acc(self.discriminant, write) &&
  0 <= self.discriminant && self.discriminant <= 1 &&
  // variant `Foo`
  (self.discriminant == 0 ==> true) &&
  // variant `Bar(X)`
  (self.discriminant == 1 ==> acc(self.elt0, write) && X(self.elt0))
}
```

### References

Rust references, mutable or otherwise, are encoded using the `val_ref` field.

```viper
field val_ref: Ref

// for some Rust type X, &mut X is the following
predicate RefMutX(self: Ref) {
  acc(self.val_ref, write) && X(self.val_ref)
}
```
