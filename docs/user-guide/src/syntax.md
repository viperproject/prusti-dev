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

## Old expressions

Old expressions are used to refer to the value that a memory location pointed at by a mutable reference had at the beginning of the function:

```rust,noplaypen
use prusti_contracts::*;

#[ensures(*x == old(*x) + 1)]
pub fn inc(x: &mut u32) {
    *x += 1;
}
```

## Implications

Implications express a [relationship](https://en.wikipedia.org/wiki/Material_conditional) between two boolean expressions:

```rust,noplaypen
#[pure]
#[ensures(result ==> self.len() == 0)]
#[ensures(!result ==> self.len() > 0)]
pub fn is_empty(&self) -> bool;
```

There is syntax for a right-to-left implication:

```rust,noplaypen
#[pure]
#[ensures(self.len() == 0 <== result)]
#[ensures(self.len() > 0 <== !result)]
pub fn is_empty(&self) -> bool;
```

As well as a biconditional ("if and only if"):

```rust,noplaypen
#[pure]
#[ensures(self.len() == 0 <==> result)]
pub fn is_empty(&self) -> bool;
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

```rust,noplaypen
#[requires(a === b)]
fn foo<T>(a: T, b: T) {}

struct X { a: i32 }

fn main() {
    foo(X { a: 1 }, X { a: 1 });
}
```

Snapshot *in*equality is expressed using the `!==` operator.

## Quantifiers

Quantifiers are typically used for describing how a method call changes a container such as a vector:

```rust,noplaypen
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
    ...
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

## Specification entailments

Specification entailments provide the contract for a given closure or function variable. See the [specification entailments](verify/spec_ent.md) chapter for more details.
