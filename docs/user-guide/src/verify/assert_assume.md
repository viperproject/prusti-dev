# Assertions and Assumptions 

You can use Prusti to verify that a certain property holds at a certain point
within the body of a function (via an assertion). It is also possible to
instruct Prusti to assume that a property holds at a certain point within a
function (via an assumption).

## Assertions

The `prusti_assert!` macro instructs Prusti to verify that a certain property
holds at a specific point within the body of a function. In contrast to the
`assert!` macro, which only accepts Rust expressions, `prusti_assert!` accepts
[specification](../syntax.md) expressions as arguments. Therefore, quantifiers
and `old` expressions are allowed within a call to `prusti_assert!`, as in
the following example:

```rust,noplaypen
#[requires(*x != 2)]
fn go(x: &mut u32) {
   *x = 2;
   prusti_assert!(*x != old(*x));
}
```

Note that the expression given to `prusti_assert!` must be side-effect free.
Therefore, certain calls might work within an `assert!`, but not within a
`prusti_assert!`. For example:

```rust,noplaypen
assert!(map.insert(5));
prusti_assert!(map.insert(5)); // error
```

`prusti_assert_eq!` and `prusti_assert_ne!` are the Prusti counterparts to
`assert_eq!` and `assert_ne!`, but the check is made for
[snapshot equality](../syntax.md#snapshot-equality), resp. snapshot inequality.

## Assumptions

The `prusti_assume!` macro instructs Prusti to assume that a certain property
holds at a point within the body of a function. Of course, if used improperly,
this can be used to introduce unsoundness. For example, Prusti would verify the
following function:

```rust,noplaypen
#[ensures(p == np)]
fn proof(p: u32, np: u32) {
  prusti_assume!(false);
}
```
