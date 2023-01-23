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

Before we implement `push`, let us briefly think of possible specifications.
Ideally, our implementation satisfies at least the following properties:

1. Executing `push` increases the length of the underlying list by one.
2. After `push(elem)` the first element of the list stores the value `elem`.
3. After executing `push(elem)`, the elements of the original list remain unchanged.

## First property

The first property can easily be expressed as a postcondition that uses the
pure method `len` introduced in the [previous chapter](new.md):

```rust,noplaypen
# #![feature(box_patterns)]
# //extern crate prusti_contracts;
# use prusti_contracts::*;
# 
# pub struct List {
#     head: Link,
# }
# 
# enum Link {
#     Empty,
#     More(Box<Node>),
# }
# 
# struct Node {
#     elem: i32,
#     next: Link,
# }
#
impl List {
#     #[pure]
#     pub fn len(&self) -> usize {
#         self.head.len()
#     }
# 
#     #[ensures(result.len() == 0)]
#     pub fn new() -> Self {
#         List {
#             head: Link::Empty,
#         }
# 
#     }
# 
    #[ensures(self.len() == old(self.len()) + 1)]
    pub fn push(&mut self, elem: i32) {
        // TODO
    }
}
#
# impl Link {
#     #[pure]
#     fn len(&self) -> usize {
#         match self {
#             Link::Empty => 0,
#             Link::More(box node) => 1 + node.next.len(),
#         }
#     }
# }
```

The above postcondition depends on *two* states, namely the state before and after
execution of `self.push(elem)`, respectively.
We use an [old expression](../syntax.md#old-expressions)
to refer to the state before execution of `self.push(elem)`.
Since we have not implemented `push` yet, Prusti will, unsurprisingly, complain:

```markdown
[Prusti: verification error] postcondition might not hold.
```

## Implementing Push

Conceptually, implementing `list.push(i)` should be straightforward:
we create a new instance of our struct for list nodes that stores
`i` in its `elem` field and the original list in its `next` field.
We may thus be tempted to write the following:


```rust,noplaypen,ignore
# #![feature(box_patterns)]
# extern crate prusti_contracts;
# use prusti_contracts::*;
# 
# pub struct List {
#     head: Link,
# }
# 
# enum Link {
#     Empty,
#     More(Box<Node>),
# }
# 
# struct Node {
#     elem: i32,
#     next: Link,
# }
#
impl List {
#     #[pure]
#     pub fn len(&self) -> usize {
#         self.head.len()
#     }
# 
#     #[ensures(result.len() == 0)]
#     pub fn new() -> Self {
#         List {
#             head: Link::Empty,
#         }
#     }
# 
    #[ensures(self.len() == old(self.len()) + 1)]
    pub fn push(&mut self, elem: i32) {
        let new_node = Box::new(Node {
            elem: elem,
            next: self.head,
        });

        self.head = Link::More(new_node);
    }
}
# 
# impl Link {
#     #[pure]
#     fn len(&self) -> usize {
#         match self {
#             Link::Empty => 0,
#             Link::More(box node) => 1 + node.next.len(),
#         }
#     }
# }
```

Unfortunately, the Rust compiler will complain about this attempt:

```markdown
[E0507] cannot move out of `self.head` which is behind a mutable reference.
```

`self` is a mutable borrow, meaning once it expires ownership to the referenced data
 returns to the original owner.
However, we moved parts of those, the original list, into our newly created node.
This would leave the borrow in a partially initialized state when it expires and would
not allow us to return ownership.
Hence, the compiler raises an error.
See [2.3: Ownership 101](https://rust-unofficial.github.io/too-many-lists/first-ownership.html)
and [2.4: Push](https://rust-unofficial.github.io/too-many-lists/first-push.html)
in the Rust tutorial for details. 

A working alternative exploits that `self` is a *mutable* borrow which allows
us to completely overwrite the referenced data.
Instead of moving the original list into the new node, we *swap* it 
with an empty list that can be returned to the owner once the borrow expires.
The [Rust standard library](https://doc.rust-lang.org/std/mem/fn.replace.html)
 provides the function `std::mem::replace` for that purpose - it moves its second
argument into the referenced first argument and returns the originally referenced value.
Using this function, the Rust compiler accepts the following implementation:


```rust,noplaypen
# #![feature(box_patterns)]
# //extern crate prusti_contracts;
# use prusti_contracts::*;
# 
use std::mem;

# pub struct List {
#     head: Link,
# }
# 
# enum Link {
#     Empty,
#     More(Box<Node>),
# }
# 
# struct Node {
#     elem: i32,
#     next: Link,
# }
# 
impl List {
#     #[pure]
#     pub fn len(&self) -> usize {
#         self.head.len()
#     }
# 
#     #[ensures(result.len() == 0)]
#     pub fn new() -> Self {
#         List {
#             head: Link::Empty,
#         }
#     }
# 
    #[ensures(self.len() == old(self.len()) + 1)]
    pub fn push(&mut self, elem: i32) {
        let new_node = Box::new(Node {
            elem: elem,
            next: mem::replace(&mut self.head, Link::Empty),
        });

        self.head = Link::More(new_node);
    }
}
# 
# impl Link {
#     #[pure]
#     fn len(&self) -> usize {
#         match self {
#             Link::Empty => 0,
#             Link::More(box node) => 1 + node.next.len(),
#         }
#     }
# }
```

In fact, the above implementation of `push` is correct.
However, attempting to verify it with Prusti still yields a verification error:

```markdown
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
This can be done with another piece of Prusti syntax:

```rust,noplaypen,ignore
#[extern_spec]
mod std {
    mod mem {
        # //extern crate prusti_contracts;
        use prusti_contracts::*;

        #[ensures(snap(dest) === src)]
        #[ensures(result === old(snap(dest)))]
        fn replace<T>(dest: &mut T, src: T) -> T;
    }
}
```

New syntax:
```rust,noplaypen,ignore
#[extern_spec(std::mem)]
#[ensures(snap(dest) === src)]
#[ensures(result === old(snap(dest)))]
fn replace<T>(dest: &mut T, src: T) -> T;
```


Lets break this code down step by step.
- First we write the Prusti annotation `#[extern_spec]` to denote that we are writing an external specification.
- Next we need to figure out where the function is located. In this case it is `std::mem`, which we then write down with `mod std { mod mem { ... } }`
- After a quick search for *\"rust std mem replace\"* we can find the [documentation for std::mem::replace](https://doc.rust-lang.org/std/mem/fn.replace.html). Here we can get the function signature: `pub fn replace<T>(dest: &mut T, src: T) -> T`. We then write down the signature in the inner module, followed by a `;`.
- To get the Prusti syntax in scope, we add `use prusti_contracts::*` to the inner module.
- Since there is no preconditions to `replace`, we don't have to write one down. The default precondition is `#[requires(true)]`.
- For writing the postcondition, we use four pieces of syntax added by Prusti:
  - `===` is called **snapshot equality** or **logical equality**. Is essentially checks if the left and right sides are structurally equal. More details can be seen [here](../syntax.md#snapshot-equality). `===` does not require the type of the compared elements to implement [PartialEq](https://doc.rust-lang.org/std/cmp/trait.PartialEq.html), which would be required if we used the standard equality operator `==`.
  - The `snap()` function takes a snapshot of a reference. This function should only be used in specifications, since it ignores the borrow checker.
  - Lastly, we have the [`old()` function](../syntax.md#old-expressions), which denotes that we want to refer to the state from before the function was called.
  - The identifier `result` is used to refer to the return parameter of the function.
- The postcondition consists of two parts, which can either be written in one condition with `&&`, or in multiple annotations like in the example above.
  - The first condition `snap(dest) === src` means: *After the function returns, the location referenced by `dest` is structurally equal to the parameter `src`*
  - The second part of the postcondition is `result === old(snap(dest))`. This means: *The `result` returned by the function is structurally equal to the the element that was referenced by `dest` **before** the function was called.*
- An important thing to note here is the Prusti does ***not*** check if `replace` actually does what the external specification says it does. `#[extern_spec]` implicitly implies the `#[trusted]` annotation, which means that any postconditions are just accepted and used by Prusti.

Depending on when you are reading this, the Rust standard library might be (partially) annotated, so this external specification may not be needed anymore.

Trusted functions can be used for verifying projects containing external code without Prusti annotations, or projects using Rust features not yet supported by Prusti.
An example is printing a string:
```rust,noplaypen
#[trusted]
fn print(s: &str) {
    println!("{s}");
}
```
Prusti will ***not*** check trusted functions for correctness. **A single incorrect specification of a trusted function can invalidate the correctness of Prusti as a whole!**
Hence, trusted functions, like unsafe Rust code, need to be treated carefully and 
require external justification.

For example, the following function will not cause the verification to fail:
```rust,noplaypen,norun
#[trusted]
fn incorrect_function() -> i32 {
    panic!()
}
```

After adding the external specification for `std::mem::replace`, we can finally verify the `push` function:

```rust,noplaypen
{{#rustdoc_include tour-src/push_property_1.rs:18:39}}

// Prusti: Verifies
```

This completes our implementation of `push` but we still need to verify
the remaining properties of its specification.

## Second property

Recall that the second property of our specification informally reads as follows:

> 2. After `push(elem)` the first element of the list stores the value `elem`.

To formally specify the above property, we first introduce another pure function, called 
`lookup`, that recursively traverses the list and returns its i-th element.
Our second desired property then corresponds to the postcondition 
`self.lookup(0) == elem`.

```rust,noplaypen
# //extern crate prusti_contracts;
# use prusti_contracts::*;
# 
# use std::mem;
# 
# pub struct List {
#     head: Link,
# }
# 
# enum Link {
#     Empty,
#     More(Box<Node>),
# }
# 
# struct Node {
#     elem: i32,
#     next: Link,
# }
# 
#  #[trusted]
#  #[ensures(old(dest.len()) == result.len())]
# fn replace(dest: &mut Link, src: Link) -> Link {
#     mem::replace(dest, src)
# }
# 
impl List {
    #[pure]
    pub fn lookup(&self, index: usize) -> i32 {
        self.head.lookup(index)
    }
# 
#     #[pure]
#     pub fn len(&self) -> usize {
#         self.head.len()
#     }
# 
#     #[ensures(result.len() == 0)]
#     pub fn new() -> Self {
#         List {
#             head: Link::Empty,
#         }
#     }
    
    #[ensures(self.len() == old(self.len()) + 1)]
    #[ensures(self.lookup(0) == elem)]
    pub fn push(&mut self, elem: i32) {
        // ...
#         let new_node = Box::new(Node {
#             elem: elem,
#             next: replace(&mut self.head, Link::Empty),
#         });
#         self.head = Link::More(new_node);
    }
}

impl Link {
    #[pure]
    pub fn lookup(&self, index: usize) -> i32 {
        match self {
            Link::More(node) => {
                if index == 0 {
                    node.elem
                } else {
                    node.next.lookup(index - 1)
                }
            },
            Link::Empty => unreachable!(),  
        }
    }
# 
#     #[pure]
#     fn len(&self) -> usize {
#         match self {
#             Link::Empty => 0,
#             Link::More(node) => 1 + node.next.len(),
#         }
#     }
} 
```

Consider the `match` statement in the last function.
The Rust compiler will complain if we attempt to omit the case `Link::Empty`.
Since there is no sensible implementation of `lookup` if the underlying list is empty,
we used the macro `unreachable!()`, which will crash the program with a panic.
Since nothing prevents us from calling `lookup` on an empty list, Prusti complains:

```markdown
unreachable!(..) statement in pure function might be reachable
```
We can specify that `lookup` should only be called on non-empty lists by adding the 
precondition `index < self.len()` to *both* `lookup` functions; this is 
sufficient to verify our second property for `push`:

```rust,noplaypen
{{#rustdoc_include tour-src/push_property_2.rs:30:33}}
    // ...
```

```rust,noplaypen
{{#rustdoc_include tour-src/push_property_2.rs:61:64}}
    // ...
```

We don't need to add the condition `0 <= index` to the precondition, since `index` has the type `usize`, so `index` is always non-negative. (If you don't want Prusti to add this condition automatically, you can add the line `encode_unsigned_num_constraint = false` to your `Prusti.toml` file).

After these changes, Prusti can successfully verify the code, so the first two properties of `push` are correct.




## Third property

The third and final property we will verify for `push` is that the original list
content is not modified:

> 3. After executing `push(elem)`, the elements of the original list remain unchanged.

To formalize the above property, we can reuse our pure function `lookup`, 
[quantifiers](../syntax.md#quantifiers), and [old expressions](../syntax.md#old-expressions), that is, we add
the postcondition:

```rust,noplaypen,ignore
{{#rustdoc_include tour-src/push_final.rs:39:41}}
```

Lets break this expression down like before:
- `forall(..)` denotes a quantifier, and it takes a [closure](https://doc.rust-lang.org/book/ch13-01-closures.html).
- The closure (denoted by the two vertical bars: `||`), takes the parameter `i: usize` and returns a `bool`. You can think of the forall expression as follows: *Any parameter passed to the closure makes it return `true`*.
  - Closures in a `forall` expression can take any number of parameters, separated by a comma: `|i: usize, j: usize|`.
- In this case we use the implication operator `==>`. It takes a left and right argument of type `bool` and is true, if the left side is false, or both sides are true. `a ==> b` is equivalent to `!a || b` and `!(a && !b)`.
  - The left side of the implication is `(1 <= i && i < self.len())`, which is the range where the right side must hold.
  - The right side is the condition for everything being shifted back by one element: `old(self.lookup(i - 1)) == self.lookup(i)))`.

## Full code listing
```rust,noplaypen
{{#include tour-src/push_final.rs}}
```