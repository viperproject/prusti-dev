# Assertions, Refutations and Assumptions 

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

## Refutations

The `prusti_refute!` macro is similar to `prusti_assert!` in its format, conditions of use and what expressions it accepts. It instructs Prusti to verify that a certain property at a specific point within the body of a function might hold in some, but not all cases. For example the following code will verify:

```rust,noplaypen
#[ensures(val < 0 ==> result == -1)]
#[ensures(val == 0 ==> result == 0)]
#[ensures(val > 0 ==> result == 1)]
fn sign(val: i32) -> i32 {
  prusti_refute!(val <= 0);
  prusti_refute!(val >= 0);
  if val < 0 {
    -1
  } else if val > 0 {
    1
  } else {
    prusti_refute!(false);
    0
  }
}
```

But the following function would not:

```rust,noplaypen
#[requires(val < 0 && val > 0)]
#[ensures(result == val/2)]
fn half(val: i32) -> i32 {
  prusti_refute!(false);
  val/2
}
```

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
