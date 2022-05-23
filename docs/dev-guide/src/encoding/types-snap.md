# Snapshot-based type encoding

Prusti's [default encoding of types](types-heap.md) heavily relies on the heap component of the Viper program state to model parts of Rust's ownership system through [permissions](http://viper.ethz.ch/tutorial/?page=1&section=#permissions).

However, some Viper features do not work well with Prusti's heap-based encoding.
For example, [quantification](http://viper.ethz.ch/tutorial/?page=1&section=#quantifiers) over structs is problematic because they are encoded using predicates instead of heap-independent types.
Similarly, since [Viper functions](http://viper.ethz.ch/tutorial/?page=1&section=#functions) must not have resource assertions in their postconditions, the heap-based encoding prevents modeling pure Rust functions that return (copyable) structures.

Prusti uses an alternative encoding of most types - called the *snapshot*-based encoding - to circumvent these issues. 
Snapshots use [Viper domains](http://viper.ethz.ch/tutorial/?page=1&section=#domains) to model each Rust type as a new (heap-independent) type in Viper
instead of relying on [Viper predicates](http://viper.ethz.ch/tutorial/?page=1&section=#predicates).

The snapshot-based encoding of a Rust type, say `T`, consists of four components:

1. A *domain type* `Snap$T` representing the Rust type `T`.
   Instances of `Snap$T` can be thought of as deep values representing a Rust value of type `T`.
2. A *constructor* function `cons$T` (for each variant of `T`) that takes all values that make up a Rust value of type `T` and returns the corresponding deep value of type `Snap$T`.
3. *Axioms* that ensure that each Rust value of type `T` corresponds to exactly one deep value of type `Snap$T` and the other way around, i.e., there is a bijection between instances of the Rust type and its snapshot encoding.
4. A heap-dependent *snapshot function* that converts the heap-based encoding of a Rust value of type `T` into a heap-independent representation of type `Snap$T`.

## Example

Consider the Rust struct declared below.
   
```rust
struct SomeStruct {
  a: i32,
  b: i32,
}
```

Prusti generates the following Viper domain covering components (1) - (3) for the above function. In particular, the single axiom ensures that two instances of `Snap$SomeStruct` are equal if and only if all of their underlying components are equal; the "only if" direction is implicit because the constructor is a function and thus produces the same value whenever the same arguments are supplied.

```viper
domain Snap$SomeStruct { // (1)
 
  // (2) 
  function cons$SomeStruct(a: Int, b: Int): Snap$SomeStruct

  // (3)
  axiom Snap$SomeStruct$injectivity {
    forall
      a1: Int, b1: Int, a2: Int, b2: Int :: { cons$SomeStruct(a1, b1), cons$SomeStruct(a2, b2) }
      cons$SomeStruct(a1, b1) == cons$SomeStruct(a2, b2) ==> a1 == a2 && b1 == b2
  }

}
```

To guarantee that there is a bijection between instances of `SomeStruct` and `Snap$SomeStruct` one needs, in principle, another axiom formalizing that every instance of `Snap$SomeStruct` corresponds to an application of the constructor function; a corresponding axiom is found below. However, we never encountered a case in which the axiom is actually needed. Prusti thus does not generate it at the moment.

```viper
axiom Snap$SomeStruct$surjectivity {
  forall
    s: Snap$SomeStruct ::
    (forall a: Int, b: Int :: {cons$SomeStruct(a, b)} s != cons$SomeStruct(a, b)) ==> false
}
```

Finally, component (4), i.e., the heap-dependent function for converting instances of `SomeStruct` in the heap-based encoding into the snapshot-based representation, is defined as follows:

```viper
// (4)
function snap$SomeStruct(self: Ref): Snap$SomeStruct
  requires acc(SomeStruct(self, read$()))
{
  unfolding acc(SomeStruct(self, read$())) in
    cons$SomeStruct(snap$i32(self.SomeStruct_a), snap$i32(self.SomeStruct_b))
}
```

The above function recursively unfolds all predicates involved in the encoding of `SomeStruct`.
It then calls the constructor of `Snap$SomeStruct`. Furthermore, for each argument, it calls the `snap$` function of the argument's type to obtain a heap-independent deep value instead of a reference.

## Primitive types

Prusti also generates `snap$` functions for primitive types such that we do not have to check whether a type is primitive or not; these functions return the primitive type itself instead of a domain type. For instance, the function `snap$i32` used in the above example is defined as follows:

```viper
function snap$i32(self: Ref): Int
  requires acc(i32(self), read$())
{
  unfolding acc(i32(self), read$()) in self.val_int
}
```
Since the snapshot types of primitive types correspond directly to Viper types, they can also be inlined:

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

Nested Rust structures are encoded as in the previous example - the main difference is that every reference to another structure needs to be replaced with the corresponding snapshot type in every constructor.

For instance, assume we extend the previous example with another structure that re-uses `SomeStruct`:

```rust
// assuming SomeStruct as before
struct BiggerStruct {
  foo: i32,
  bar: SomeStruct,
}
```

In this case, Prusti generates another domain type for `BiggerStruct` whose constructor takes a snapshot type for every instance of `SomeStruct`; analogously, its snapshot function invokes `snap$SomeStruct` to convert references to `SomeStruct` into deep values of type `Snap$SomeStruct`: 

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

## Enumerations

> **This feature is not fully implemented in Prusti yet.**

While the snapshot-based encoding of enumerations is mostly analogous to the encoding of structs, it needs to account for multiple enum *variants*, which are distinguished by an integer-valued discriminant. Consequently, the snapshot domain generated for an enumeration is slightly more involved:

- It contains one constructor for each variant of the enumeration.
- It contains one injectivity axiom for each variant.
- It additionally needs to ensure that different constructors yield different snapshot values. To this end, we introduce a new domain function mapping every snapshot value to its enumeration discriminant - an integer representing the variant. Moreover, for each variant, we add an axiom expressing that constructors yield snapshot values with the correct discriminant.
- Its heap-dependent `snap$` function needs to branch over the enumeration's `discriminant` field to select the correct constructor when converting a reference to a snapshot value.

For example, consider the enumeration below, which defines a custom Option type.

```rust
// assuming SomeStruct as before
enum MyOption {
  _Some(SomeStruct),
  _None,
}
```

The corresponding snapshot encoding is defined as follows:

```viper
domain Snap$MyOption {
  // one constructor for each variant
  function cons$MyOption$0(): Snap$MyOption
  function cons$MyOption$1(x: Snap$SomeStruct): Snap$MyOption

  // injectivity axioms for all constructors with parameters
  axiom Snap$MyOption$injectivity$1 {
    forall
      i: Snap$SomeStruct, j: Snap$SomeStruct :: { cons$MyOption$1(i), cons$MyOption$1(j) }
      cons$MyOption$1(i) == cons$MyOption$1(j) ==> i == j
  }

  // map snapshot values to variant discriminant
  function discriminant$MyOption(x: Snap$MyOption): Int

  // axiom defining possible discriminant values 
  axiom Snap$MyOption$discriminants {
    forall
      x: Snap$MyOption :: 
      discriminant$MyOption(x) == 0 || discriminant$MyOption(x) == 1
  }

  // one axiom characterizing the discriminant for each constructor
  axiom Snap$MyOption$0 {
    discriminant$MyOption(cons$MyOption$0()) == 0
  }
  
  axiom Snap$MyOption$1 {
    forall
      i: Snap$SomeStruct :: { cons$MyOption$1(i) } 
      discriminant$MyOption(cons$MyOption$1(i)) == 1
  }
}

// heap-dependent function for computing snapshot values
function snap$MyOption(x: Ref): Snap$MyOption
  requires acc(MyOption(x), read$())
{
  // call the cons function matching the discriminant
  unfolding acc(MyOption(x), read$()) in 
    x.discriminant == 1
      ? unfolding acc(MyOption$_Some(x.enum_val), read$()) in
          cons$MyOption$1(snap$SomeStruct(x.enum_val))
      : cons$MyOption$0()
}
```

## Applications of snapshots 

Prusti makes use of the heap-independent encoding of types via snapshots 
to implement several features, which are collected below.

### Structural equality

Prusti uses the snapshot-based encoding for checking whether two instances of a data structure are equal. That is, both `x == y` and `std::cmp::eq(x,y)` are encoded as a comparison of the snapshot values of `x` and `y`:

```viper
snap$Type(x) == snap$Type(y)
```

Inequalities `x != y` are encoded analogously. 

Notice that Prusti only uses snapshots for a subset of *supported* types. More precisely, a type `T` has to meet the following conditions:

1. `T` automatically derives the trait [`Eq`](https://doc.rust-lang.org/std/cmp/trait.Eq.html).
2. `T` is composed of other supported types, i.e., primitive types and other types that derive `Eq`.

If a type does not meet these criteria, it either invokes a user-supplied custom implementation or a bodyless stub function.

### Comparing return values of pure functions

Whenever one invokes a [pure function](pure.md) with equal arguments, the function should yield the same return value, i.e., a function `f` with one argument should satisfy the following specification:

```
x == y  ==> f(x) == f(y)
```

For non-recursive types, the snapshot function `snap$type(ref)` recursively unfolds the predicate encoding the type of `ref`. Hence, the above property holds whenever equality of the type of `x` and `y` corresponds to structural equality, i.e., whenever the `Eq` trait is automatically derived. 

For example, the following piece of Rust code verifies while internally using snapshots to discharge equality checks:

```rust
// as before, but derives Eq
#[derive(PartialEq, Eq)]
struct SomeStruct {
  a: i32,
  b: i32,
}

#[pure]
#[requires(x == y)]
#[ensures(result == y.a)]
fn foo(x: SomeStruct, y: SomeStruct) -> i32 {
  x.a
}

#[requires(x == y)]
#[ensures(result == 2 * foo(x))]
fn test(x: SomeStruct, y: SomeStruct) -> i32 {
    foo(x) + foo(y)
}
```

However, the snapshot function cannot completely unfold potentially unbounded recursive types.
To enable the same behavior as specified above, Prusti thus introduces a shortcut that enables lazy evaluation of snapshot functions: For each pure function `f` that takes a recursive type (that also derives `Eq`) as an argument, it generates a domain function `mirror$f` - called the *mirror function* - that takes snapshots instead of references as arguments.
In the postcondition of `f`, Prusti then links the return values of `f` to the return value of `mirror$f`: Both functions are required to yield the same return value whenever `mirror$f` is invoked on the snapshot of `f`'s argument. 
The code snippet below outlines this encoding.

```viper
domain Mirrors {
  function mirror$f(x: Snap$SomeRecStruct) : Int
}

function f(x:Ref) : Int
  requires SomeRecStruct(x)
  ensures [result == mirror$f(snap$SomeRecStruct(x)), true]
{
  // ... 
}
```

### Pure functions returning copy types

Prusti uses snapshots to encode [pure Rust functions](pure.md) that return structures or enumerations.
This is necessary because Viper does not allow resource assertions within the postcondition of functions.
At the moment, only types implementing the [`Copy`](https://doc.rust-lang.org/core/marker/trait.Copy.html) trait are supported.

As an example, assume both the struct `BiggerStruct` and the struct `SomeStruct` from previous examples derive the traits `Copy` and `Eq`.
Moreover, consider the following pure function `get` mapping every instance of `BiggerStruct` to its wrapped instance of `SomeStruct`:

```rust
#[pure]
fn get(x: BiggerStruct) -> SomeStruct {
  x.bar
}
```

Prusti encodes the function `get` as a Viper function that first computes the result of `get` and then invokes the snapshot function `snap$SomeStruct` to return a snapshot value instead of a reference:

```viper
// snapshot domains are encoded as in previous examples
function get(x: Ref): Snap$SomeStruct
  requires BiggerStruct(x)
{
  unfolding BiggerStruct(x) in snap$SomeStruct(x.bar)
}
```

At the call site, the returned snapshot value is transformed into the default heap-based encoding by first havocking the involved reference and then assuming that the reference's snapshot coincides with the returned snapshot value:

```viper
// encoding of x = get(y)
var x: Ref 
x := builtin$havoc_ref()
inhale acc(SomeStruct(x), write) && snap$SomeStruct(x) == get(y)
```

> **Warning:** Pure functions returning non-primitive types are partially supported by Prusti.
> In particular, chaining pure functions, e.g., `f(g(h(x, y)))`, and constructing new
> instances of Copy types within pure functions is currently not fully supported.

### Quantification over structures

> **TODO**: Has this been added in the context of closures?
