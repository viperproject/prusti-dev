# Specification syntax

Prusti specifications are a superset of Rust boolean expressions. They must be deterministic and side-effect free. Therefore, they can only call only [pure functions](verify/pure.md). The extensions to Rust expressions are summarized below:

| Syntax | Meaning |
| --- | --- |
| [`old(...)`](#old-expressions) | Value of expression in a previous state |
| [`... ==> ...`](#implications) | Implication |
| [`... <== ...`](#implications) | Implication |
| [`... <==> ...`](#implications) | Biconditional |
| [`... === ...`](#snapshot-equality) | Snapshot equality |
| [`... !== ...`](#snapshot-equality) | Snapshot inequality |
| [`forall(...)`](#quantifiers) | Universal quantifier |
| [`exists(...)`](#quantifiers) | Existential quantifier |
| [<code>... &#x7C;= ...</code>](#specification-entailments) | Specification entailment |


## `result` Variable

When using Prusti, `result` is used to refer to what a function returns.
`result` can only be used inside a postcondition, meaning that variables called `result` used in a function need to be renamed.

Here is an example for returning an integer:
```rust,noplaypen,ignore
# use prusti_contracts::*;
# 
#[ensures(result == 5)]
fn five() -> i32 {
    5
}
```

And an example for returning a tuple and accessing individual fields:
```rust,noplaypen,ignore
# use prusti_contracts::*;
# 
#[ensures(result.0 / 2 == result.1 && result.2 == 'a')]
fn tuple() -> (i32, i32, char) {
    (10, 5, 'a')
}
```


## Old Expressions

Old expressions are used to refer to the value that a memory location pointed at by a mutable reference had at the beginning of the function:

```rust,noplaypen,ignore
# use prusti_contracts::*;
# 
#[ensures(*x == old(*x) + 1)]
pub fn inc(x: &mut u32) {
    *x += 1;
}
```


## Implications

Implications express a [relationship](https://en.wikipedia.org/wiki/Material_conditional) between two boolean expressions:

```rust,noplaypen,ignore
# use prusti_contracts::*;
# 
#[pure]
#[ensures(result ==> self.len() == 0)]
#[ensures(!result ==> self.len() > 0)]
pub fn is_empty(&self) -> bool {
    // ...
}
```

`a ==> b` is equivalent to `!a || b` and `!(a && !b)`. Here you can see a truth table for the implication operator:

| `a`   | `b`   | `a ==> b` |
|-------|-------|-----------|
| `false` | `false` | `true`      |
| `false` | `true`  | `true`      |
| `true` | `false` | `false`     |
| `true` | `true`  | `true`      |

Note: The expression `b` is only evaluated if `a` is true ([Short-circuit evaluation](https://en.wikipedia.org/wiki/Short-circuit_evaluation)).

There is also syntax for a right-to-left implication:

```rust,noplaypen,ignore
# use prusti_contracts::*;
# 
#[pure]
#[ensures(self.len() == 0 <== result)]
#[ensures(self.len() > 0 <== !result)]
pub fn is_empty(&self) -> bool;
```

As well as a biconditional ("if and only if"):

```rust,noplaypen,ignore
# use prusti_contracts::*;
# 
#[pure]
#[ensures(self.len() == 0 <==> result)]
pub fn is_empty(&self) -> bool {
    // ...
}
```

Semantically, a biconditional is equivalent to a Boolean `==`. However, it has lower precedence than the `==` operator.

## Snapshot Equality

Snapshot equality (`===`) compares the
[snapshots](https://viperproject.github.io/prusti-dev/dev-guide/encoding/types-snap.html)
of two values; essentially checking if the two values are structurally equal. In
contrast, the standard equality (`==`) between values is determined by the
implementation of
[`PartialEq`](https://doc.rust-lang.org/std/cmp/trait.PartialEq.html). These two
equalities do not necessarily coincide. For example, some types do not implement
`PartialEq`, or their implementation cannot be encoded as a pure function.
Nonetheless, snapshot equality could be used to compare values of such types, as
in the following code:

```rust,noplaypen,ignore
# use prusti_contracts::*;
# 
#[requires(a === b)]
fn foo<T>(a: T, b: T) {}

struct X { a: i32 }

fn main() {
    foo(X { a: 1 }, X { a: 1 });
}
```

There is also the counterpart for `!=` for checking structural inequality: `!==`.

## `snap` Function
The function `snap` can be used to take a snapshot of a reference in specifications.
Its functionality is similar to the `clone` function, but `snap` is only intended for use in specifications. It also does not require the type behind the reference to implement the `Clone` trait:
```rust,noplaypen,ignore
fn snap<T>(input: &T) -> T {
    // ...
}
```

The `snap` function enables writing specifications that would otherwise break Rusts ownership rules:
```rust,noplaypenm,ignore
# use prusti_contracts::*;
# 
struct NonCopyInt {
    value: i32
}

#[ensures(x === old(x))] // Error: Cannot borrow "*x" mutably
fn do_nothing_1(x: &mut NonCopyInt) {}

#[ensures(snap(x) === old(snap(x)))]
fn do_nothing_2(x: &mut NonCopyInt) {}
```
In the first function, `x` will be borrowed by the `old` function, and can therefore not be used in the snapshot equality `===` at the same time.
Using `snap(x)` will create a snapshot of `x`, almost like using `x.clone()`, but only for specifications and even for `x` that cannot be cloned normally.

## Quantifiers

Quantifiers are typically used for describing how a method call changes a container such as a vector:

```rust,noplaypen,ignore
# use prusti_contracts::*;
# 
#[requires(0 <= index && index < self.len())]
#[ensures(self.len() == old(self.len()))]
#[ensures(self.lookup(index) == value)]
#[ensures(
    forall(|i: usize|
        (0 <= i && i < self.len() && i != index)
        ==> (self.lookup(i) == old(self.lookup(i)))
    )
)]
pub fn store(&mut self, index: usize, value: i32) {
    // ...
}
```

There may be multiple bound variables:

```plain
forall(|x: isize, y: isize| ...)
```

The syntax of universal quantifiers is:

```plain
forall(|<bound variable>: <bound variable type>, ...| <filter> ==> <expression>)
```

and the syntax of existential ones:

```plain
exists(|<bound variable>: <bound variable type>, ...| <expression>)
```

## Adding specification in trait `impl` blocks

Adding specifications to trait functions requires the `impl` block to be annotated with `#[refine_trait_spec]`:

```rust,noplaypen,ignore
# use prusti_contracts::*;
# 
trait TestTrait {
    fn trait_fn(self) -> i64;
}

#[refine_trait_spec] // <== Add this annotation
impl TestTrait for i64 {

    // Cannot add these 2 specifications without `refine_trait_spec`:
    #[requires(true)]
    #[ensures(result >= 0)]
    fn trait_fn(self) -> i64 {
        5
    }
}
```

Note: Currently there is no clear error message when `#[refine_trait_spec]` is missing, you will just get an error message on the `requires` or the `ensures` like this one:
```plain
[E0407] method `prusti_pre_item_trait_fn_d5ce99cd719545e8adb9de778a953ec2` is not a member of trait `TestTrait`.
```
See [issue #625](https://github.com/viperproject/prusti-dev/issues/625) for more details.


## Specification entailments

Specification entailments provide the contract for a given closure or function variable. See the [specification entailments](verify/spec_ent.md) chapter for more details.
