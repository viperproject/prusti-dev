# Push

> **Recommended reading:** 
> [2.4: Push](https://rust-unofficial.github.io/too-many-lists/first-push.html)
>

## Informal specifications

Our next goal is to implement and verify a method that pushes an integer onto a list.
In contrast to methods like `len`, `push` modifies the list; it thus takes
`&mut self` as its first argument:

```rust,noplaypen,ignore
impl List {
    pub fn push(&mut self, elem: i32) {
        // TODO
    }
}
```

Since `push` modifies `self`, it cannot be marked as a `#[pure]` function (it has a side effect on `self`). This means we will not be able to use `push` inside specifications for other functions later.

Before we implement `push`, let us briefly think of possible specifications.
Ideally, our implementation satisfies at least the following properties:

1. Executing `push` increases the length of the underlying list by one. [(Chapter link)](push.md#first-property)
2. After `push(elem)` the first element of the list stores the value `elem`. [(Chapter link)](push.md#second-property)
3. After executing `push(elem)`, the elements of the original list remain unchanged, but are moved back by 1 position. [(Chapter link)](push.md#third-property)

## Initial code

We start out with an implementation of `push`. If you want to learn more about how this code works, you can read [2.4: Push](https://rust-unofficial.github.io/too-many-lists/first-push.html), where it is explained in detail.

Here is our initial code:

```rust,noplaypen
{{#rustdoc_include ../../../../prusti-tests/tests/verify/pass/user-guide/push_initial_code.rs:initial_code}}
```

## First property

The first property can easily be expressed as a postcondition that uses the
pure method `len` introduced in the [previous chapter](new.md):

```rust,noplaypen
{{#rustdoc_include ../../../../prusti-tests/tests/verify/pass/user-guide/push_property_1.rs:property_1}}
// Prusti: Verifies
```

With this, the first of the three properties of `push` is verified, but we still have two more to prove.

## Note about external specifications

Prusti verifies the above implementation of `push`, but this might come as a surprise: the implementation calls the standard library method `std::mem::replace`. How does Prusti know what this method does? Prusti performs *function modular* verification, so calls to other methods only use that method's specifications, and never its implementation (which may not even be available, or may use unsupported features).

The answer is that the `prusti-std` crate provides specifications for *some* of the most common standard library methods, including `std::mem::replace`. In situations where `prusti-std` does not (yet) provide a suitable specification for a method used in the code, an *external specification* must be declared. Creating external specifications is discussed in the [`prusti-std` and External Specifications](extern_specs.md) chapter of this guide.

## Trusted functions

External specifications, like the one for `std::mem::replace` provided by `prusti-std`, are implicitly `#[trusted]` by Prusti.
Trusted functions can be used for verifying projects containing external code that does not have Prusti annotations, or projects using Rust features that are not yet supported by Prusti.
An example is printing a string slice (not supported yet):
```rust,noplaypen
# // The next line is only required for doctests, you can ignore/remove it
# extern crate prusti_contracts;
# use prusti_contracts::*;
# 
#[trusted]
fn print(s: &str) {
    println!("{s}");
}
```
Prusti will ***not*** check trusted functions for correctness, so it is the programmers responsibility to check their the specification manually. **A single incorrect specification of a trusted function can invalidate the correctness of Prusti as a whole!**
Hence, trusted functions, like unsafe Rust code, need to be treated carefully and 
require external justification.

For example, the following function will not cause the verification to fail:
```rust,noplaypen,norun
# // The next line is only required for doctests, you can ignore/remove it
# extern crate prusti_contracts;
# use prusti_contracts::*;
# 
#[trusted]
fn incorrect_function() -> i32 {
    panic!()
}
```

This one is even worse, it will enable anything to be verified:
```rust,noplaypen,norun
# // The next line is only required for doctests, you can ignore/remove it
# extern crate prusti_contracts;
# use prusti_contracts::*;
#
#[trusted]
#[ensures(false)]
fn wrong() {}
```

## Second property

Recall the second property of our specification:

> 2. After `push(elem)`, the first element of the list stores the value `elem`.

To formally specify the above property, we first introduce another pure function, called 
`lookup`, that recursively traverses the list and returns its i-th element.
Our second desired property then corresponds to the postcondition 
`self.lookup(0) == elem`.

```rust,noplaypen
{{#rustdoc_include ../../../../prusti-tests/tests/verify/fail/user-guide/push_property_2_missing_bounds.rs:lookup}}
```

Consider the `match` statement in the last function.
The Rust compiler will complain if we attempt to omit the case `Link::Empty`.
We have no sensible implementation of `lookup` if the underlying list is empty,
so we used the macro `unreachable!()`, which will crash the program with a panic.
Since nothing prevents us from calling `lookup` on an empty list, Prusti complains:

```plain
unreachable!(..) statement might be reachable
```

We can specify that `lookup` should only be called with an `index` between `0` and `self.len()` (which implies that we cannot call lookup on an empty list: `0 <= index < self.len()` implies `0 < self.len()`). We do this by adding the precondition `index < self.len()` to *both* `lookup` functions.
This is sufficient to verify our second property for `push`:

```rust,noplaypen
{{#rustdoc_include ../../../../prusti-tests/tests/verify/pass/user-guide/push_property_2_with_bounds.rs:bounds}}
```

We don't need to add the condition `0 <= index`, since `index` has the type `usize`, and unsigned integers are always non-negative. (If you don't want Prusti to add this condition automatically, you can add the line `encode_unsigned_num_constraint = false` to your `Prusti.toml` file).

After these changes, Prusti can successfully verify the code, so the first two properties of `push` are correct.

## Third property

The third and final property we will verify for `push` is that the original list
content is not modified:

> 3. After executing `push(elem)`, the elements of the original list remain unchanged (just shifted back by one).

To formalize the above property, we can reuse our pure function `lookup`, 
[quantifiers](../syntax.md#quantifiers), and [old expressions](../syntax.md#old-expressions), that is, we add
the postcondition:

```rust,noplaypen
{{#rustdoc_include ../../../../prusti-tests/tests/verify/pass/user-guide/push_final_code.rs:shifted_back}}
```

Let's break this expression down like before:
- We start with the `ensures` annotation, to denote a postcondition.
- `forall(..)` denotes a [quantifier](../syntax.md#quantifiers). The variables and body of a quantifier use a syntax similar to Rust [closures](https://doc.rust-lang.org/book/ch13-01-closures.html).
- The two vertical bars: `||` contain the variables that the quantifier quantifies over. Here we only have one parameter `i: usize`. The type of the quantifier body is `bool`. You can think of the `forall` expression as follows: *Any values chosen for the quantified variables should result in the expression evaluating to `true`*.
- In this case, the quantifier uses the [implication operator `==>`](../syntax.md#implications). It takes a left and right argument of type `bool` and is true if the left-hand side is false, or both sides are true.
  - The left-hand side of the implication is `(1 <= i && i < self.len())`, which is the range where the right side must hold. If the index `i` is outside of this range, we don't care about it, so the condition will be false, making the entire implication true.
  - The right-hand side is the condition for everything being shifted back by one element: `old(self.lookup(i - 1)) == self.lookup(i)))`. Note that the right side is only evaluated if the left side is true, otherwise there would be an overflow in `i - 1` for `i == 0`, or a panic if `i` is out of bounds.

This code is verified successfully by Prusti, so we know that the `lookup` function satisfies the three postconditions!


## Full code listing

```rust,noplaypen
// Expand to see full code up to this chapter
{{#rustdoc_include ../../../../prusti-tests/tests/verify/pass/user-guide/push_final_code.rs:nothing}}
```