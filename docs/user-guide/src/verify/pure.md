# Pure functions

Pure functions are functions which are deterministic and side-effect free. In Prusti, such functions can be marked with the `#[pure]` attribute. They can take shared references as arguments, but they cannot take mutable references, because modifying the heap is considered a side effect.

At the moment, it is up to the user to ensure that functions annotated with `#[pure]` always terminate. Non-terminating pure functions would allow to infer `false`.

```rust,noplaypen,ignore
use prusti_contracts::*;

#[pure]
#[ensures(result == *a + *b)]
fn pure_example(a: &i32, b: &i32) -> i32 {
  *a + *b
}

#[ensures(*c == a + b)]
fn impure_example(a: &i32, b: &i32, c: &mut i32) {
  *c = *a + *b
}
```
