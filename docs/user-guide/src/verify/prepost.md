# Pre- and postconditions

In Prusti, the externally observable behaviour of a function can be specified with preconditions and postconditions. They can be provided using [Rust attributes](https://doc.rust-lang.org/reference/attributes.html):

```rust,noplaypen,ignore
use prusti_contracts::*;

#[requires(...)]
#[ensures(...)]
fn example() { ... }
```

`#[requires(...)]` is a precondition, `#[ensures(...)]` is a postcondition. There can be any number (including none) of preconditions and postconditions attached to a function. When no precondition is specified, `#[requires(true)]` is assumed, and likewise for postconditions. The expression inside the parentheses of `requires` or `ensures` should be a [Prusti specification](../syntax.md).

Preconditions are checked whenever the given function is called. Postconditions are checked at any exit point of the function, i.e. explicit `return` statements, as well as the end of the function body.
