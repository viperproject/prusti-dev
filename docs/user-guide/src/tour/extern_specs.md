# `prusti-std` and External Specifications

In the previous chapters, the code we verified included calls to functions provided by the standard library, such as `std::mem::replace`. Prusti verifies code in a *function modular* fashion, so it only considers the specification of a function in order to verify a call to it. By default, external functions are assumed to have the contract `#[requires(true)]`, `#[ensures(true)]`, i.e. it is always possible to call the function, but it does not guarantee anything.

`prusti-std` is a crate that is part of the Prusti project. It provides specifications for some standard library methods. It does not provide specifications for *all* standard library methods, but the aim is to provide a high coverage of calls, based on data found in real Rust code, evaluated on the top crates of `crates.io`.

The documentation of `prusti-std` provides an overview of the specified methods, as well as informal descriptions of the contracts.

## Creating new external specifications

When the specification for an external method is not provided (for example, because it is not in `prusti-std`), it is likely that verification of code using that method will fail. To provide the contract for an external method, an [*external specification*](../verify/external.md) should be declared.

For the sake of example, assume the `std::mem::replace` method was *not* specified in `prusti-std`. We could provide an external specification for it like so:

```rust,ignore
#[extern_spec(std::mem)]
#[ensures(snap(dest) === src)]
#[ensures(result === old(snap(dest)))]
fn replace<T>(dest: &mut T, src: T) -> T;
```

Let's break this snippet down step by step:
- First, we write the Prusti annotation `#[extern_spec]` to denote that we are writing an external specification. This requires `prusti_contracts::*` to be imported first.
- Next, we need to declare where the original function is located. In this case it is the module `std::mem`, so we put its path in the parameter: `#[extern_spec(std::mem)]`
- After a quick search for *\"rust std mem replace\"* we can find the [documentation for std::mem::replace](https://doc.rust-lang.org/std/mem/fn.replace.html). Here we can get the function signature: `pub fn replace<T>(dest: &mut T, src: T) -> T`. We then write down the signature in the inner module, followed by a `;`. The visibility modifier is omitted for external specifications.
- Since there are no preconditions to `replace`, we can use the (implicit) default `#[requires(true)]`.
- For writing the postcondition, we use four pieces of Prusti syntax:
  - [`===`](../syntax.md#snapshot-equality) is called **snapshot equality** or **logical equality**. Is means that the left and right operands are structurally equal. `===` does not require the type of the compared elements to implement [PartialEq](https://doc.rust-lang.org/std/cmp/trait.PartialEq.html), which would be required if we used the standard equality operator `==`.
  - The [`snap()`](../syntax.md#snap-function) function takes a snapshot of a reference. It has a similar functionality to the [`clone()`](https://doc.rust-lang.org/std/clone/trait.Clone.html) method, but does not require the type of the reference it is called on to implement the `Clone` trait. `snap` should only be used in specifications, since it ignores the borrow checker.
  - Lastly, we have the [`old()` function](../syntax.md#old-expressions), which denotes that we want to refer to the state of `snap(dest)` from before the function was called.
  - The identifier [`result`](../syntax.md#result-variable) is used to refer to the return parameter of the function.
- The postcondition consists of two parts, which can either be written in one condition with `&&`, or in multiple `#[ensures(...)]` annotations like in the example above.
  - The first condition `snap(dest) === src` means: *After the function returns, the location referenced by `dest` is structurally equal to the parameter `src`.*
  - The second part of the postcondition is `result === old(snap(dest))`. This means: *The `result` returned by the function is structurally equal to the the element that was referenced by `dest` **before** the function was called.*

Since `result` is structurally equal to `dest` from before the function call, Prusti knows that the pure function `len()` called on `result` returns the same value as it would have for `dest`.

An important thing to note here is that Prusti does ***not*** check if `replace` actually does what the external specification says it does. `#[extern_spec]` implicitly implies the `#[trusted]` annotation, which means that any postconditions are just accepted and used by Prusti.

### Future

There is currently new functionality planned for Prusti-assistant, which should enable the user to automatically generate the `extern_spec` declaration for a given call.
