# Snapshot-based type encoding

Because the [heap-based approach](types-heap.md) refers to the heap of the program state, it is not always possible to use it, e.g. due to not having the required permissions. Snapshots circumvent this problem by encoding the memory representation of any Rust value into an abstract Viper [domain](http://viper.ethz.ch/tutorial/?page=1&section=#domains) type.

```rust
// for a Rust type
struct SomeStruct {
  a: i32,
  b: i32,
}
```

```viper
domain Snap$SomeStruct {
  function cons$SomeStruct(a: Int, b: Int): Snap$SomeStruct

  axiom Snap$SomeStruct$injectivity {
    forall
      a1: Int, b1: Int, a2: Int, b2: Int :: { cons$SomeStruct(a1, b1), cons$SomeStruct(a2, b2) }
      cons$SomeStruct(a1, b1) == cons$SomeStruct(a2, b2) ==> a1 == b1 && a2 == b2
  }

  axiom Snap$SomeStruct$surjectivity {
    forall
      s: Snap$SomeStruct ::
      (forall a: Int, b: Int :: {cons$SomeStruct(a, b)} s != cons$SomeStruct(a, b)) ==> false
  }
}
```

The domain above consists of three components:

1. The constructor which takes all the primitive values that make up a Rust composite value and outputs an instance of the abstract `Snap$SomeStruct` type. Instances of `Snap$SomeStruct` cannot be manipulated directly, but axioms (defined next) allow the verifier to make use of them.
2. The injectivity axiom that states that if two instances of `Snap$SomeStruct` are equal, all their components are equal.
3. The surjectivity axiom that states that any instance of `Snap$SomeStruct` must correspond to some combination of primitive value inputs.

Together, the injectivity and surjectivity axioms establish the bijectivity of the snapshot encoding.

In addition to the snapshot encoding, a function that converts Viper values from `Ref`s to snapshot types is generated:

```viper
// SomeStruct predicate defined as in heap-encoding

function snap$SomeStruct(self: Ref): Snap$SomeStruct
  requires acc(SomeStruct(self, read$()))
{
  unfolding acc(SomeStruct(self, read$())) in
    cons$SomeStruct(snap$i32(self.SomeStruct_a), snap$i32(self.SomeStruct_b))
}
```

## Primitive types

The snapshot encoding for primitive types can be expressed as:

```viper
// for Rust i32
function snap$i32(self: Ref): Int
  requires acc(i32(self), read$())
{
  unfolding acc(i32(self), read$()) in self.val_int
}
```

Since the snapshot types of primitive types correspond directly to Viper types, these functions can be inlined into the composite type snapshots that use them:

```viper
// SomeStruct as above

function snap$SomeStruct(self: Ref): Snap$SomeStruct
  requires acc(SomeStruct(self, read$()))
{
  unfolding acc(SomeStruct(self, read$())) in
    unfolding acc(i32(self.SomeStruct_a), read$()) in
    unfolding acc(i32(self.SomeStruct_b), read$()) in
      cons$SomeStruct(self.SomeStruct_a.val_int, self.SomeStruct_b.val_int)
}
```

## Nested structures

Nested Rust structures re-use the snapshot encoding of its component types:

```rust
// assuming SomeStruct as before
struct BiggerStruct {
  foo: i32,
  bar: SomeStruct,
}
```

```viper
domain Snap$BiggerStruct {
  function cons$BiggerStruct(foo: Int, bar: Snap$SomeStruct): Snap$BiggerStruct

  // axioms ...
}

function snap$BiggerStruct(self: Ref): Snap$BiggerStruct
  requires acc(BiggerStruct(self, read$()))
{
  unfolding acc(BiggerStruct(self, read$())) in
    cons$BiggerStruct(snap$i32(self.BiggerStruct_foo), snap$SomeStruct(self.BiggerStruct_bar))
}
```

## Mirrors

```viper
domain SnapshotMirrors {
  function mirror_hello(a: Int): Int
}

function hello(a: Int): Int
  requires true
  ensures result == mirror_hello(a)
{
  !(a < 3) ? (!(a > 10) ? 10 : a - 2) : a + 2
}
```

TODO
