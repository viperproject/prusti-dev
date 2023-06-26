# Assertions, Refutations and Assumptions 

You can use Prusti to verify that a certain property holds at a certain point
within the body of a function (via an assertion). It is also possible to
instruct Prusti to assume that a property holds at a certain point within a
function (via an assumption).

## Assertions

The macros `prusti_assert!`, `prusti_assert_eq!` and `prusti_assert_ne!` instruct Prusti to verify that a certain property holds at a specific point within the body of a function. In contrast to the `assert!`, `assert_eq!` and `assert_ne!` macros, which only accept Rust expressions, the Prusti variants accept [specification](../syntax.md) expressions as arguments. Therefore, [quantifiers](../syntax.md#quantifiers), [`old`](../syntax.md#old-expressions) expressions and other Prusti specification syntax is allowed within a call to `prusti_assert!`, as in the following example:

```rust,noplaypen,ignore
# // The next line is only required for doctests, you can ignore/remove it
# extern crate prusti_contracts;
# use prusti_contracts::*;
# 
#[requires(*x != 2)]
fn go(x: &mut u32) {
   *x = 2;
   prusti_assert!(*x != old(*x));
}
```

The two macros `prusti_assert_eq!` and `prusti_assert_ne!` are also slightly different than their standard counterparts, in that they use [snapshot equality](../syntax.md#snapshot-equality) `===` instead of [Partial Equality](https://doc.rust-lang.org/std/cmp/trait.PartialEq.html) `==`.

```rust,noplaypen,ignore
# // The next line is only required for doctests, you can ignore/remove it
# extern crate prusti_contracts;
# use prusti_contracts::*;
# 
#[requires(a === b)]
fn equal(a: u64, b: u64) {
    // these 2 lines do the same:
    prusti_assert!(a === b);
    prusti_assert_eq!(a, b);
}

#[requires(a !== b)]
fn different(a: u64, b: u64) {
    // these 2 lines do the same:
    prusti_assert!(a !== b);
    prusti_assert_ne!(a, b);
}
```

Note that the expression given to `prusti_assert!` must be side-effect free, since they will not result in any runtime code. Therefore, using code containing [impure](../verify/pure.md) functions will work in an `assert!`, but not within a `prusti_assert!`. For example:

```rust,noplaypen,ignore
# // The next line is only required for doctests, you can ignore/remove it
# extern crate prusti_contracts;
# use prusti_contracts::*;
# 
# fn test(map: std::collections::HashMap) {
assert!(map.insert(5));
prusti_assert!(map.insert(5)); // error
# }
```

Using Prusti assertions instead of normal assertions can speed up verification, because every `assert!` results in a branch in the code, while `prusti_assert!` does not.

## Refutations

> Refutation **should not be relied upon for soundness** as they may succeed even when expected to fail; Prusti may not be able to prove the property being refuted and thus won't complain even though the property actually holds (e.g. if the property is difficult to prove).

The `prusti_refute!` macro is similar to `prusti_assert!` in its format, conditions of use and what expressions it accepts. It instructs Prusti to verify that a certain property at a specific point within the body of a function might hold in some, but not all cases. For example the following code will verify:

```rust,noplaypen
# // The next line is only required for doctests, you can ignore/remove it
# extern crate prusti_contracts;
# use prusti_contracts::*;
# 
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

```rust,noplaypen,ignore
# // The next line is only required for doctests, you can ignore/remove it
# extern crate prusti_contracts;
# use prusti_contracts::*;
# 
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

```rust,noplaypen,ignore
# // The next line is only required for doctests, you can ignore/remove it
# extern crate prusti_contracts;
# use prusti_contracts::*;
# 
#[ensures(p == np)]
fn proof(p: u32, np: u32) {
    prusti_assume!(false);
}
```
