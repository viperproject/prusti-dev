# Specification syntax

Prusti specifications are a superset of Rust boolean expressions. They must be deterministic and side-effect free. Therefore, they can only call only [pure functions](verify/pure.md). The extensions to Rust expressions are summarized below:

| Syntax | Meaning |
| --- | --- |
| [`old(...)`](#old-expressions) | Value of expression in a previous state |
| [`... ==> ...`](#implications) | Implication |
| [`forall(...)`](#quantifiers) | Universal quantifier |
| [`exists(...)`](#quantifiers) | Existential quantifier |
| [<code>... &#x7C;= ...</code>](#specification-entailments) | Specification entailment |

## Old expressions

Old expressions are used to refer to the value that a memory location pointed at by a mutable reference had at the beginning of the function:

```rust
extern crate prusti_contracts;
use prusti_contracts::*;

#[ensures(*x == old(*x) + 1)]
pub fn inc(x: &mut u32) {
    *x += 1;
}
```

## Implications

Implications express a [relationship](https://en.wikipedia.org/wiki/Material_conditional) between two boolean expressions:

```rust
#[pure]
#[ensures(result ==> self.len() == 0)]
#[ensures(!result ==> self.len() > 0)]
pub fn is_empty(&self) -> bool;
```

There is no syntax for logical equivalences ("if and only if"), because this coincides with `==`:

```rust
#[pure]
#[ensures(result == (self.len() == 0))]
pub fn is_empty(&self) -> bool;
```

## Quantifiers

Quantifiers are typically used for describing how a method call changes a container such as a vector:

```rust
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
