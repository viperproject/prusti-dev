# Resources and obligations

One way of describing state that is otherwise not captured by a Prusti program is using resources and obligations. They are typically produced and consumed by [`#[trusted]`](trusted.md) functions that have some external effects (e.g. by calling functions in foreign non-Rust libraries or by interacting with the real world).

Resources and obligations can appear in the pre- and postconditions of functions. When a function is called, Prusti must prove that all resources in its precondition are held by the caller at the call site. Calling a function then has the effect of
- removing the resources in its precondition from and
- adding the resources in its postcondition to

the caller's state at the call site.

## Resources

A resource can be declared, for example, like so:

```rust,noplaypen,ignore
enum Currency {
    CAD,
    CHF,
    DKK,
}

resource! {
    fn cash(amount: usize, currency: Currency);
}
```

The general syntax is

```rust,noplaypen,ignore
resource! {
    fn resource_name(amount: usize, ...);
}
```

where `resource_name` can be an arbitrary identifier and `...` here stands for arbitrary function parameters. The first parameter always has to be `amount: usize` (literally) and it has special semantics: it expresses how many resource instances a particular invocation of the resource represents. This means that, for example, asserting `cash(2, Currency::CHF)` is equivalent to asserting `cash(1, Currency::CHF) & cash(1, Currency::CHF)`.

Example program:

```rust,noplaypen
{{#rustdoc_include ../../../../prusti-tests/tests/verify/pass/user-guide/resources_apples.rs:code}}
// Prusti: VERIFIES
```

In the above example, Prusti is able to prove that if the trusted functions have the effects they claim they do (e.g. in the case of `buy_apple`, it removes at most CHF 2 from some hypothetical account of ours and it produces at least one apple in a hypothetical warehouse), then the non-trusted `buy_apple_in_canada` also fulfills its contract (it consumes at most CAD 4 and produces at least 1 apple). Note that the program still verifies if the `4` in `cash(4, Currency::CAD)` is increased to any number larger than `4` because in such a case, there are still enough resources for the `exchange()` calls. Compare this to obligations in a section below.

In a more realistic scenario, resources can be used to establish lower and upper bounds for the number of calls of a particular function. In the following example, by making a call of `costly_function` consume one instance of `call_credits`, we have a natural way of proving upper bounds on the number of times the function is called.

```rust,noplaypen,ignore
resource! {
    fn call_credits(amount: usize);
}

#[trusted]
#[requires(call_credits(1))]
fn costly_function(arg: i32) {
    // ...
}

#[requires(call_credits(2))]
fn costly_at_most_twice(arg: i32) {
    costly_function(arg);
    if arg > 0 {
        costly_function(arg - 1);
    }
}

#[requires(call_credits(10))]
fn complicated_procedure() {
    // ... costly_function(...) ... costly_at_most_twice(...) ...

    // if this program verifiers, we know that this function calls
    // `costly_function` at most ten times
}
```

The same idea is used to prove lower and upper bounds on the running time of functions as explained in the chapter about [time reasoning](time_reasoning.md).

Resources can also be asserted in universal quantifiers and [loop invariants](loop.md):

```rust,noplaypen
{{#rustdoc_include ../../../../prusti-tests/tests/verify/pass/user-guide/resources_clean_rooms.rs:code}}
// Prusti: VERIFIES
```

## Usage of resources in expressions

The Rust functions associated with resources may not be called or otherwise referenced outside of specification code (preconditions, postconditions, `prusti_assert!`, etc.). Inside specification code, they may only appear
- alone,
- as conjuncts with other expressions inside the non-short-circuiting And (`&`),
- inside the consequent of an implication,
- inside the body of a universal quantifier,
- inside the then- or else-branch of a conditional.

They are not allowed in other kinds expressions. In particular, not inside
- negations,
- non-short-circuiting disjunctions (`|`),
- the antecedents of implications,
- the bodies of existential quantifiers,
- the guards of conditionals.

The short-circuiting `&&` and `||` are equivalent to conditionals:
- `A && B` is equivalent to `if A { B } else { false }`, and
- `A || B` is equivalent to `if A { true } else { B }`.

Therefore, resources are allowed to appear on the left-hand side of `&&` and `||` but not on the right-hand side.

## Pure functions
Resources may appear in the preconditions of [`#[pure]`](pure.md) functions but not in their postconditions. When a pure function is called, the resources in the precondition are asserted (so verification fails if Prusti cannot prove that the caller has all the required resources), but they are not removed from the caller's state.

> Note: The behavior of resources in the contracts of pure functions as described here might be not fully implemented yet and it might change in the future.

## Obligations

Obligations are declared and used almost identically to resources. The only two differences are

* obligations are declared using the `obligation!` macro instead of `resource!`, but otherwise, the declarations have the same structure, and
* for a program to verify, Prusti must prove that no instances of obligations are leaked.

Obligations are leaked if at the end of a function, not all obligations that are held are asserted in the function postcondition or if from one loop iteration to another, more obligations are acquired than what the change of the obligations asserted in the [loop invariant](loop.md) is.

In the following example, `with_resources` verifies, but `with_obligations` doesn't because obligations are leaked.

```rust,noplaypen
{{#rustdoc_include ../../../../prusti-tests/tests/verify/fail/user-guide/resources_vs_obligations.rs:code}}
// Prusti: FAILS
```

Obligations are primarily used for proving that all allocated resources are eventually deallocated. If we have only one trusted function which allocates some kind of objects and only one function which deallocates them, we can annotate the allocating function with `#[ensures(obligation_name(...))]` and the deallocating one with `#[requires(obligation_name(...))]`. Then if our program verifier, we have the guarantee that for an arbitrary function, all objects allocated by it are also deallocated by it or are asserted in its postcondition. See the example below.

```rust,noplaypen
{{#rustdoc_include ../../../../prusti-tests/tests/verify/fail/user-guide/obligation_leak.rs:code}}
// Prusti: FAILS
```

`procedure1` verifies successfully. For `procedure2`, on the other hand, we get a verification error because if it exits through the `return;`, the allocated object does not get deallocated.

## Loops
When a [loop](loop.md) is encountered, only as many resources are taken from the currently executing function's state as the loop invariant in the first iteration asserts. At the end of the loop, as many resources are given back to the state of the enclosing function as the loop invariant in the last iteration asserts (plus/minus those produced/consumed in the last iteration after the invariant).

Naturally then, it is not considered an obligation leak when the loop invariant in the first loop iteration doesn't assert all obligations currently held in the enclosing function since those that are not asserted just stay in the function's state for after the loop and are in that sense not leaked.

Hence, an obligation leak inside a loop occurs only when the amount of an obligation held in one loop iteration increases more than the amount of this obligation asserted in the loop invariant.

By this logic, the following program verifies.

```rust,noplaygen
{{#rustdoc_include ../../../../prusti-tests/tests/verify/pass/user-guide/loop_resource_partial_assert.rs:code}}
// Prusti: VERIFIES
```

## `prusti_exhale!` and `prusti_inhale!`

`prusti_exhale!` and `prusti_inhale!` are close companions of [`prusti_assert!` and `prusti_assume!`](assert_refute_assume.md). They allow the full [Prusti specification syntax](../syntax.md) and for assertions that don't access any resources (here, we use _resources_ to refer to both _resources_ and _obligations_), `prusti_exhale!(...)` does the same as `prusti_assert!(..)` and `prusti_inhale!(...)` the same as `prusti_assume!(...)`. If the assertion contains resources, `prusti_exhale!` consumes them and `prusti_inhale!` produces them. Here are several examples of functions that verify:

```rust,noplaypen
{{#rustdoc_include ../../../../prusti-tests/tests/verify/pass/user-guide/inhale_exhale.rs:code}}
// Prusti: VERIFIES
```

and here a few that don't:

```rust,noplaypen
{{#rustdoc_include ../../../../prusti-tests/tests/verify/fail/user-guide/inhale_exhale.rs:code}}
// Prusti: FAILS
```

Similarly to `prusti_assume!`, `prusti_exhale!` and `prusti_inhale!` may introduce unsoundness. They can be a helpful tool for trying out verification approaches or debugging verification errors, which is what they are primarily meant to be used for.
