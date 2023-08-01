## Specifications in trait `impl` blocks

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

Note: The current error message returned when `#[refine_trait_spec]` is missing does not hint at how to fix the issue. A message like this will be shown on either `requires` or `ensures`: 
```plain
[E0407]
method `prusti_pre_item_trait_fn_d5ce99cd719545e8adb9de778a953ec2`
is not a member of trait `TestTrait`.
```
See [issue #625](https://github.com/viperproject/prusti-dev/issues/625) for more details.
