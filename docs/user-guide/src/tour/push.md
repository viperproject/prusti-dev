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

Since `push` modifies `self`, it cannot be marked as a `#[pure]` function. This means we will not be able to use `push` inside specifications for other functions later.

Before we implement `push`, let us briefly think of possible specifications.
Ideally, our implementation satisfies at least the following properties:

1. Executing `push` increases the length of the underlying list by one.
2. After `push(elem)` the first element of the list stores the value `elem`.
3. After executing `push(elem)`, the elements of the original list remain unchanged (just moved back by 1).

## Initial code

We start out with an implementation of `push`. If you want to learn more about how this code works, you can read [2.4: Push](https://rust-unofficial.github.io/too-many-lists/first-push.html), where it is explained in detail.

Here is our initial code:

```rust,noplaypen,ignore
{{#rustdoc_include tour-src/src/push/initial_code.rs:initial_code}}
```

## First property

The first property can easily be expressed as a postcondition that uses the
pure method `len` introduced in the [previous chapter](new.md):

```rust,noplaypen
{{#rustdoc_include tour-src/src/push/property_1.rs:property_1}}
```

Even though the above implementation of `push` is correct, attempting to verify it with Prusti still yields a verification error:

```plain
[Prusti: verification error] postcondition might not hold.
```

This error may look surprising at first: 
We create a new list node that stores the the original list in its next field.
Why is Prusti unable to realize that the length of the resulting list
is one plus the length of the original list?

The explanation is that Prusti performs *function modular* verification, 
that is, it only uses a function's specification (instead of also consulting the 
function's implementation) whenever it encounters a function call.
The only exception are *pure* functions, such as `len`, where Prusti also takes the
function body into account.

In our case, the function `std::mem::replace` is neither marked as `pure` nor does it
come with a specification. Hence, Prusti assumes that it is memory safe and nothing else.
That is, Prusti uses `true` as both pre- and postcondition of `std::mem::replace`,
which is too weak to prove the specification of `push`: according to its specification,
`std::mem::replace` could arbitrarily change the original list and thus also its length.
Hence, we cannot conclude that the length the list returned by
`mem::replace(&mut self.head, Link::Empty)` coincides with the length of the original 
list.

We can remedy this issue by strengthening the specification of `std::mem::replace`.
In this tutorial, we will assume that the standard library is correct, that is, we 
do not attempt to verify specifications for functions in external crates, 
like `std::mem::replace`. To this end, we have to add the specification to the function.
This can be done with another piece of Prusti syntax, the [extern_spec](../verify/external.md):

```rust,noplaypen,ignore
{{#rustdoc_include tour-src/src/push/property_1.rs:extern_spec}}
```

Lets break this code down step by step.
- First we write the Prusti annotation `#[extern_spec]` to denote that we are writing an external specification. This requires `prusti_contracts::*` to be imported first.
- Next we need to figure out where the function is located. In this case it is `std::mem`, which we then put as the parameter in `#[extern_spec(std::mem)]`
- After a quick search for *\"rust std mem replace\"* we can find the [documentation for std::mem::replace](https://doc.rust-lang.org/std/mem/fn.replace.html). Here we can get the function signature: `pub fn replace<T>(dest: &mut T, src: T) -> T`. We then write down the signature in the inner module, followed by a `;`.
- Since there are no preconditions to `replace`, we can use the (implicit) default `#[requires(true)]`.
- For writing the postcondition, we use four pieces of Prusti syntax:
  - `===` is called **snapshot equality** or **logical equality**. Is essentially checks if the left and right sides are structurally equal. More details can be seen [here](../syntax.md#snapshot-equality). `===` does not require the type of the compared elements to implement [PartialEq](https://doc.rust-lang.org/std/cmp/trait.PartialEq.html), which would be required if we used the standard equality operator `==`.
  - The [`snap()`](../syntax.md#snap-function) function takes a snapshot of a reference. It has a similar functionality to the `clone()` method, but does not require the type of the reference it is called on to implement the `Clone` trait. `snap` should only be used in specifications, since it ignores the borrow checker.
  - Lastly, we have the [`old()` function](../syntax.md#old-expressions), which denotes that we want to refer to the state of `snap(dest)` from before the function was called.
  - The identifier [`result`](../syntax.md#result-variable) is used to refer to the return parameter of the function.
- The postcondition consists of two parts, which can either be written in one condition with `&&`, or in multiple `#[ensures(...)]` annotations like in the example above.
  - The first condition `snap(dest) === src` means: *After the function returns, the location referenced by `dest` is structurally equal to the parameter `src`*
  - The second part of the postcondition is `result === old(snap(dest))`. This means: *The `result` returned by the function is structurally equal to the the element that was referenced by `dest` **before** the function was called.*

Since `result` is structurally equal to `dest` from before the function call, Prusti knows that the pure function `len()` called on `result` returns the same value as it would have for `dest`.


An important thing to note here is the Prusti does ***not*** check if `replace` actually does what the external specification says it does. `#[extern_spec]` implicitly implies the `#[trusted]` annotation, which means that any postconditions are just accepted and used by Prusti.

### Future

There is currently new functionality planed for Prusti-assistant, which should enable the user to automatically generate parts of the `extern_spec` syntax.

There is also work being done for providing external specifications for the Rust standard library. Depending on when you are reading this, the `std::mem::replace` function might be annotated already, in that case this `extern_spec` may not be needed anymore.
You can track the progress and find some already completed specifications [in this Pull Request](https://github.com/viperproject/prusti-dev/pull/1249),

## Trusted Functions

As mentioned above, `extern_specs` are implicitly `#[trusted]` by Prusti.
Trusted functions can be used for verifying projects containing external code that does not have Prusti annotations, or projects using Rust features that are not yet supported by Prusti.
An example is printing a string slice (not supported yet):
```rust,noplaypen
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
# use prusti_contracts::*;
# 
#[trusted]
fn incorrect_function() -> i32 {
    panic!()
}
```

This one is even worse, this will enable anything to be verified:
```rust,noplaypen,norun
# use prusti_contracts::*;
# 
#[trusted]
#[ensures(false)]
fn wrong() {}
```

### Checking the `extern_spec`

Let's get back to our code. After adding the external specification for `std::mem::replace`, we can finally verify the `push` function:

```rust,noplaypen
{{#rustdoc_include tour-src/src/push/property_1.rs:property_1}}

// Prusti: Verifies
```

With this, the first or our three property of `push` is verified, but we still have 2 more to prove.

## Second property

Recall that the second property of our specification informally reads as follows:

> 2. After `push(elem)` the first element of the list stores the value `elem`.

To formally specify the above property, we first introduce another pure function, called 
`lookup`, that recursively traverses the list and returns its i-th element.
Our second desired property then corresponds to the postcondition 
`self.lookup(0) == elem`.

```rust,noplaypen
{{#rustdoc_include tour-src/src/push/property_2_missing_bounds.rs:lookup}}
```

Consider the `match` statement in the last function.
The Rust compiler will complain if we attempt to omit the case `Link::Empty`.
Since there is no sensible implementation of `lookup` if the underlying list is empty,
we used the macro `unreachable!()`, which will crash the program with a panic.
Since nothing prevents us from calling `lookup` on an empty list, Prusti complains:

```plain
unreachable!(..) statement in pure function might be reachable
```

We can specify that `lookup` should only be called with an `index` which is between `0` and `self.len()` (which implies that we cannot call lookup on an empty list). We do this by adding the precondition `index < self.len()` to *both* `lookup` functions. This is 
sufficient to verify our second property for `push`:

```rust,noplaypen
{{#rustdoc_include tour-src/src/push/property_2_with_bounds.rs:bounds}}
```

We don't need to add the condition `0 <= index` to the precondition, since `index` has the type `usize`, and unsigned integers are always non-negative. (If you don't want Prusti to add this condition automatically, you can add the line `encode_unsigned_num_constraint = false` to your `Prusti.toml` file).

After these changes, Prusti can successfully verify the code, so the first two properties of `push` are correct.




## Third property

The third and final property we will verify for `push` is that the original list
content is not modified:

> 3. After executing `push(elem)`, the elements of the original list remain unchanged (just shifted back by one).

To formalize the above property, we can reuse our pure function `lookup`, 
[quantifiers](../syntax.md#quantifiers), and [old expressions](../syntax.md#old-expressions), that is, we add
the postcondition:

```rust,noplaypen,ignore
{{#rustdoc_include tour-src/src/push/final_code.rs:shifted_back}}
```

Lets break this expression down like before:
- We start with the `ensures` annotation, to denote a postcondition.
- `forall(..)` denotes a quantifier, and it takes a [closure](https://doc.rust-lang.org/book/ch13-01-closures.html).
- The closure is denoted by the two vertical bars: `||`, which contain the parameters it the closure takes. Here we only have one parameter `i: usize`. The return type of the closure is `bool`. You can think of the `forall` expression as follows: *Any parameter passed to the closure makes it return `true`*.
  - Closures in a `forall` expression can take any number of parameters, separated by a comma: `|i: usize, j: usize|`.
- In this case, the closure uses the [implication operator `==>`](../syntax.md#implications). It takes a left and right argument of type `bool` and is true, if the left side is false, or both sides are true.
  - The left side of the implication is `(1 <= i && i < self.len())`, which is the range where the right side must hold. If the index `i` is outside of this range, we don't care about it, so the condition will be false, making the entire implication true.
  - The right side is the condition for everything being shifted back by one element: `old(self.lookup(i - 1)) == self.lookup(i)))`.

This code is verified successfully by Prusti, so we know that the `lookup` function correctly implements the three postconditions!


## Full code listing

```rust,noplaypen
// Expand to see full code up to this chapter
{{#rustdoc_include tour-src/src/push/final_code.rs:nothing}}
```