# Pop

> **Recommended reading:** 
> [2.5: Pop](https://rust-unofficial.github.io/too-many-lists/first-pop.html), 

Let's continue with a function to remove and return one element from the top of a list. The way to write such a function is described in [2.5: Pop](https://rust-unofficial.github.io/too-many-lists/first-pop.html), we will focus on the verification in this chapter.

We will rename the `pop` function to `try_pop`. The return type is still `Option<i32>` and `try_pop` will only return `Some(item)` if the list has elements, and `None` otherwise. We will then add a new `pop` function, which has the return type `i32`, and will panic if it is called with an empty list. However, by using the correct precondition, we can prevent the `pop` function to ever panic! Here is the code:

```rust,noplaypen
{{#rustdoc_include tour-src/src/pop/initial_code.rs:initial}}
```

For the implementation of our `pop` method, we can reuse the implementation of `try_pop`. We call `try_pop` on the list, then call `unwrap` on the result. `unwrap` will return the inner value of the `Option` if it is `Some`, and will panic otherwise.
Normally, it is bad form to use `unwrap` in production code, where you should handle potential errors, instead of just panicing.
But, since we are verifying that there will never be `None` passed to `unwrap`, we should be able to get away with it here.

## Properties of `try_pop`

Lets start by (informally) listing the properties we want our `try_pop` method to have.
We do not need a precondition for `try_pop`, since it can be called on any list.
This just leaves all the postconditions, which can be put into two categories:

- The input list is empty before the call
  1. The `result` will be `None`
  2. The list will still be empty
- The input list is not empty before the call
  1. The `result` will not be `None`
  2. The `result` will contain the first value of the old list
  3. The length will get reduced by one
  4. All elements will be shifted forwards by one

## Properties of `pop`

For `pop`, we will add a precondition that the list is not empty.
The postconditions are similar to those of `try_pop`, but we can skip all those that only apply to empty lists:

1. The `result` will be the first value of the old list
2. The length will get reduced by one
3. All elements will be shifted forwards by one

## Implementing the specification

### Adding `List::is_empty`

Since we will need to check if a list is empty, we can implement a `#[pure]` `is_empty` function for List. It can just call the `is_empty` function on `self.head`:

```rust,noplaypen
{{#rustdoc_include tour-src/src/pop/initial_code.rs:is_empty}}
```

### Precondition of `pop`

Let's start our specification with the precondition of `pop`. Since the `unwrap` will panic if it is passed `None`, and `try_pop` returns `None` if the list is empty, we have to ensure that `pop` is only called on non-empty lists. Therefore we add it as a precondition:

```rust,noplaypen
{{#rustdoc_include tour-src/src/pop/initial_code.rs:pop_precondition}}
```

`try_pop` does not require a precondition, since it will not panic on an empty list, but instead just return `None`.

### `try_pop` postcondition for empty lists

Now we will implement the two conditions that hold for `try_pop` if you pass an empty list to it.
To ensures that these are only checked for empty lists, we use the implication operator `==>` again:

```rust,noplaypen
{{#rustdoc_include tour-src/src/pop/final_code.rs:try_pop_empty}}
```

This specification ensures that for empty lists, the list will still be empty afterwards, and `try_pop` will return `None`.

### Checking if the correct result is returned

Now we can add the specification for checking if the correct result is returned. Like with `push`, we will use the `lookup` function for checking that the `result` is the old head of the list. For this we call `lookup(0)` on a snapshot of `self` before the function call: `old(snap(self)).lookup(0)`.

We can check this condition for snapshot equality with `result`. This will always hold for `pop`, since the list is never empty:

```rust,noplaypen
{{#rustdoc_include tour-src/src/pop/final_code.rs:pop_result_correct}}
```

For `try_pop`, condition only holds if the list was not empty before the call. In addition, the `result` is an `Option::Some`, so we will have to include this in our postcondition:

```rust,noplaypen
{{#rustdoc_include tour-src/src/pop/final_code.rs:try_pop_result_correct}}
```


### Using `predicate!` to reduce code duplication

You may have noticed that the last two conditions for `pop` are the same as the last two of `try_pop`. We could just write the same conditions twice, but we can also place them in a Prusti [`predicate`](../verify/predicate.md) and then use that `predicate` in both specifications.

A `predicate` is basically just a [`pure`](../verify/pure.md) function that returns a `bool`, but it can use all the additional syntax available in Prusti specifications. Lets look at an example:

```rust,noplaypen
predicate! {
    fn larger_than_5(x: i32) -> bool {
        x > 5
    }
}

#[requires(larger_than_5(input))]
#[ensures(larger_than_5(result))]
fn add_one(input: i32) -> i32 {
    input + 1
}
```

In our specific case, we want to have a predicate to compare the state of the list before the call to the state afterwards. The `old` function cannot be used inside a predicate, we have to pass the two states as separate arguments. For this we write a `predicate` takes 2 arguments, which represent the state after and before the function. Such a predicate is also called a `two-state predicate`.
Note that we take both arguments by (immutable) reference, since we don't need the predicate to take ownership over the arguments:

```rust,noplaypen,ignore
# use prusti_contracts::*;
# 
impl List {
    predicate! {
        fn head_removed(&self, prev: &Self) -> bool {
            // ...
        }
    }
}
```

The 2 parameters are called `self` and `prev`, both with the type `&Self`.

The goal of this predicate is to check if the head of a list was correctly removed.
For this we need check two properties:
1. The new length is the old length minus one
2. Each element is shifted forwards by one

We combine these two properties into a single expression using `&&`:

```rust,noplaypen
{{#rustdoc_include tour-src/src/pop/final_code.rs:two_state_predicate}}
```

Here we are able to call `.len()` and `.lookup()` on both references, because they are pure functions.

To use this predicate, we call it on the list `self`, and then pass in a snapshot of the `self` from before the function call. Like with the condition for correctness of the `result`, we can just add this `predicate` to `pop`, but we need to restrict it to non-empty lists for `try_pop`:

```rust,noplaypen
{{#rustdoc_include tour-src/src/pop/final_code.rs:predicate_use}}
```

## Summary

We have now implemented the entire specification we formulated at the start of this chapter!
The list should now be able to correctly `push`, `pop`, `try_pop` elements, as described in our specifications.

But how do we know that our specifications match the behavior of the code? We will look at this in the next chapter.

If you want the full code we have now, expand the code block below:

```rust,noplaypen
// Expand to see full code up to this chapter
{{#rustdoc_include tour-src/src/pop/final_code.rs:none}}
```