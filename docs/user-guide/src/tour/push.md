# Push

> **Recommended reading:** 
> [2.4: Push](https://rust-unofficial.github.io/too-many-lists/first-push.html)
>

## Informal specifications

Our next goal is to implement and verify a method that pushes an integer onto a list.
In contrast to methods like `len`, `push` modifies the list; it thus takes
`&mut self` as its first argument:

```rust,noplaypen
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
#use prusti_contracts::*;
#
#pub struct List {
#    head: Link,
#}
#
#enum Link {
#    Empty,
#    More(Box<Node>),
#}
#
#struct Node {
#    elem: i32,
#    next: Link,
#}
#
impl List {
#    #[pure]
#    pub fn len(&self) -> usize {
#        self.head.len()
#    }
#
#    #[ensures(result.len() == 0)]
#    pub fn new() -> Self {
#        List {
#            head: Link::Empty,
#        }
#
#    }
#
    #[ensures(self.len() == old(self.len()) + 1)]
    pub fn push(&mut self, elem: i32) {
        // TODO
    }
}
#
#impl Link {
#    #[pure]
#    fn len(&self) -> usize {
#        match self {
#            Link::Empty => 0,
#            Link::More(box node) => 1 + node.next.len(),
#        }
#    }
#}
```

The above postcondition depends on *two* states, namely the state before and after
execution of `self.push(elem)`, respectively.
We use an [old expression](../syntax.md#old-expressions)
to refer to the state before execution of `self.push(elem)`.
Since we have not implemented `push` yet, Prusti will, unsurprisingly, complain:

```
[Prusti: verification error] postcondition might not hold.
```

## Implementing Push

Conceptually, implementing `list.push(i)` should be straightforward:
we create a new instance of our struct for list nodes that stores
`i` in its `elem` field and the original list in its `next` field.
We may thus be tempted to write the following:


```rust,noplaypen
# #![feature(box_patterns)]
#use prusti_contracts::*;
#
#pub struct List {
#    head: Link,
#}
#
#enum Link {
#    Empty,
#    More(Box<Node>),
#}
#
#struct Node {
#    elem: i32,
#    next: Link,
#}
#
impl List {
#    #[pure]
#    pub fn len(&self) -> usize {
#        self.head.len()
#    }
#
#    #[ensures(result.len() == 0)]
#    pub fn new() -> Self {
#        List {
#            head: Link::Empty,
#        }
#    }
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
#impl Link {
#    #[pure]
#    fn len(&self) -> usize {
#        match self {
#            Link::Empty => 0,
#            Link::More(box node) => 1 + node.next.len(),
#        }
#    }
#}
```

Unfortunately, the Rust compiler will complain about this attempt:

```
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
#use prusti_contracts::*;
#
use std::mem;

#pub struct List {
#    head: Link,
#}
#
#enum Link {
#    Empty,
#    More(Box<Node>),
#}
#
#struct Node {
#    elem: i32,
#    next: Link,
#}
#
impl List {
#    #[pure]
#    pub fn len(&self) -> usize {
#        self.head.len()
#    }
#
#    #[ensures(result.len() == 0)]
#    pub fn new() -> Self {
#        List {
#            head: Link::Empty,
#        }
#    }
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
#impl Link {
#    #[pure]
#    fn len(&self) -> usize {
#        match self {
#            Link::Empty => 0,
#            Link::More(box node) => 1 + node.next.len(),
#        }
#    }
#}
```

In fact, the above implementation of `push` is correct.
However, attempting to verify it with Prusti still yields a verification error:

```
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
like `std::mem::replace`.
To this end, we introduce a [trusted](../verify/trusted.md) wrapper function `replace`
that calls `std::mem::replace` and is equipped with the desired specification.
The attribute `#[trusted]` tells Prusti to assume the provided specification is correct
without attempting to verify it against a function's body.

After introducing a trusted wrapper that ensures that `replace` does not change the 
length of the original list, the following implementation verifies:

```rust,noplaypen
# #![feature(box_patterns)]
#use prusti_contracts::*;
#
#use std::mem;
#
#pub struct List {
#    head: Link,
#}
#
#enum Link {
#    Empty,
#    More(Box<Node>),
#}
#
#struct Node {
#    elem: i32,
#    next: Link,
#}
#
#[trusted]
#[ensures(old(dest.len()) == result.len())]
fn replace(dest: &mut Link, src: Link) -> Link {
    mem::replace(dest, src)
}

impl List {
#    #[pure]
#    pub fn len(&self) -> usize {
#        self.head.len()
#    }
#
#    #[ensures(result.len() == 0)]
#    pub fn new() -> Self {
#        List {
#            head: Link::Empty,
#        }
#    }
#
    #[ensures(self.len() == old(self.len()) + 1)]
    pub fn push(&mut self, elem: i32) {
        let new_node = Box::new(Node {
            elem: elem,
            next: replace(&mut self.head, Link::Empty),
        });

        self.head = Link::More(new_node);
    }
}
#
#impl Link {
#    #[pure]
#    fn len(&self) -> usize {
#        match self {
#            Link::Empty => 0,
#            Link::More(box node) => 1 + node.next.len(),
#        }
#    }
#}
// Prusti: VERIFIES
```

Trusted functions are useful for dealing with external code, like `std::mem::replace`, 
or constructs that are not yet supported by Prusti.
**However, a single incorrect specification of a trusted function can invalidate the
 correctness of Prusti as a whole!**
Hence, trusted functions, like unsafe Rust code, need to be treated carefully and 
require external justification.

It is good practice to provide strong preconditions for trusted functions 
to reduce the chance that they are accidentially called with unintended arguments.
In our case, we could additionally require that `replace` always takes an empty
list as its second argument.
We formalize this precondition by introducing another pure function `is_empty`:

```rust,noplaypen
# #![feature(box_patterns)]
#use prusti_contracts::*;
#
#use std::mem;
#
#pub struct List {
#    head: Link,
#}
#
#enum Link {
#    Empty,
#    More(Box<Node>),
#}
#
#struct Node {
#    elem: i32,
#    next: Link,
#}
#
#[trusted]
#[requires(src.is_empty())]
#[ensures(dest.is_empty())]
#[ensures(old(dest.len()) == result.len())]
fn replace(dest: &mut Link, src: Link) -> Link {
    mem::replace(dest, src)
}

#impl List {
#    #[pure]
#    pub fn len(&self) -> usize {
#        self.head.len()
#    }
#
#    #[ensures(result.len() == 0)]
#    pub fn new() -> Self {
#        List {
#            head: Link::Empty,
#        }
#    }
#
#    #[ensures(self.len() == old(self.len()) + 1)]
#    pub fn push(&mut self, elem: i32) {
#        let new_node = Box::new(Node {
#            elem: elem,
#            next: replace(&mut self.head, Link::Empty),
#        });
#
#        self.head = Link::More(new_node);
#    }
#}
#
impl Link {
#    #[pure]
#    fn len(&self) -> usize {
#        match self {
#            Link::Empty => 0,
#            Link::More(box node) => 1 + node.next.len(),
#        }
#    }
#
    #[pure]
    fn is_empty(&self) -> bool {
        match self {
            Link::Empty => true,
            Link::More(box node) => false,
        }
    }
}
// Prusti: VERIFIES
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
# #![feature(box_patterns)]
#use prusti_contracts::*;
#
#use std::mem;
#
#pub struct List {
#    head: Link,
#}
#
#enum Link {
#    Empty,
#    More(Box<Node>),
#}
#
#struct Node {
#    elem: i32,
#    next: Link,
#}
#
# #[trusted]
# #[ensures(old(dest.len()) == result.len())]
#fn replace(dest: &mut Link, src: Link) -> Link {
#    mem::replace(dest, src)
#}
#
impl List {
    #[pure]
    pub fn lookup(&self, index: usize) -> i32 {
        self.head.lookup(index)
    }
#
#    #[pure]
#    pub fn len(&self) -> usize {
#        self.head.len()
#    }
#
#    #[ensures(result.len() == 0)]
#    pub fn new() -> Self {
#        List {
#            head: Link::Empty,
#        }
#    }
    
    #[ensures(self.len() == old(self.len()) + 1)]
    #[ensures(self.lookup(0) == elem)]
    pub fn push(&mut self, elem: i32) {
        // ...
#        let new_node = Box::new(Node {
#            elem: elem,
#            next: replace(&mut self.head, Link::Empty),
#        });
#        self.head = Link::More(new_node);
    }
}

impl Link {
    #[pure]
    pub fn lookup(&self, index: usize) -> i32 {
        match self {
            Link::More(box node) => {
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
#    #[pure]
#    fn len(&self) -> usize {
#        match self {
#            Link::Empty => 0,
#            Link::More(box node) => 1 + node.next.len(),
#        }
#    }
}
```

Consider the `match` statement in the last function.
The Rust compiler will complain if we attempt to omit the case `Link::Empty`.
Since there is no sensible implementation of `lookup` if the underlying list is empty,
we used the macro `unreachable!()`, which will crash the program with a panic.
Since nothing prevents us from calling `lookup` on an empty list, Prusti complains:

```
unreachable!(..) statement in pure function might be reachable
```
We can specify that `lookup` should only be called on non-empty lists by adding the 
precondition `0 <= index && index < self.len()` to *both* `lookup` functions; this is 
sufficient to verify our second property for `push`:


```rust,noplaypen
# #![feature(box_patterns)]
#use prusti_contracts::*;
#
#use std::mem;
#
#pub struct List {
#    head: Link,
#}
#
#enum Link {
#    Empty,
#    More(Box<Node>),
#}
#
#struct Node {
#    elem: i32,
#    next: Link,
#}
#
# #[trusted]
# #[ensures(old(dest.len()) == result.len())]
#fn replace(dest: &mut Link, src: Link) -> Link {
#    mem::replace(dest, src)
#}
#
impl List {
    #[pure]
    #[requires(0 <= index && index < self.len())]
    pub fn lookup(&self, index: usize) -> i32 {
        self.head.lookup(index)
    }
#
#    #[pure]
#    pub fn len(&self) -> usize {
#        self.head.len()
#    }
#
#    #[ensures(result.len() == 0)]
#    pub fn new() -> Self {
#        List {
#            head: Link::Empty
#        }
#    }
#
#    #[ensures(self.len() == old(self.len()) + 1)]
#    pub fn push(&mut self, elem: i32) {
#        let new_node = Box::new(Node {
#            elem: elem,
#            next: replace(&mut self.head, Link::Empty),
#        });
#        self.head = Link::More(new_node);
#    }
}

impl Link {
    #[pure]
    #[requires(0 <= index && index < self.len())]
    pub fn lookup(&self, index: usize) -> i32 {
        // ...
#        match self {
#            Link::More(box node) => {
#                if index == 0 {
#                    node.elem
#                } else {
#                    node.next.lookup(index - 1)
#                }
#            },
#            Link::Empty => unreachable!(),
#        }
    }
#
#    #[pure]
#    fn len(&self) -> usize {
#        match self {
#            Link::Empty => 0,
#            Link::More(box node) => 1 + node.next.len(),
#        }
#    }
}
// Prusti: VERIFIES
```

## Third property

The third and final property we will verify for `push` is that the original list
content is not modified:

> 3. After executing `push(elem)`, the elements of the original list remain unchanged.

To formalize the above property, we can reuse our pure function `lookup`, 
[quantifiers](../syntax.md#quantifiers), and [old expressions](../syntax.md#old-expressions), that is, we add
the postcondition:

```rust,noplaypen
#[ensures(forall(|i: usize| (1 <= i && i < self.len()) ==>
             old(self.lookup(i - 1)) == self.lookup(i)))] 
pub fn push(&mut self, elem: i32) {
    // ...
}
```

After adding the above postcondition, Prusti will complain that the postcondition
might not hold; the reason is similar to an issue we encountered when verifying
the first property: the specification of `replace` is too weak.
Verification succeeds after adding the same postcondition to `replace`.
We conclude this section with the full code for verifying `push`:

```rust,noplaypen
# #![feature(box_patterns)]
#use prusti_contracts::*;
#
#use std::mem;
#
#pub struct List {
#    head: Link,
#}
#
#enum Link {
#    Empty,
#    More(Box<Node>)
#}
#
#struct Node {
#    elem: i32,
#    next: Link,
#}
#
#[trusted]
#[requires(src.is_empty())]
#[ensures(dest.is_empty())]
#[ensures(old(dest.len()) == result.len())]
#[ensures(forall(|i: usize| (0 <= i && i < result.len()) ==>
                old(dest.lookup(i)) == result.lookup(i)))]
fn replace(dest: &mut Link, src: Link) -> Link {
    mem::replace(dest, src)
}

impl List {
#    #[pure]
#    #[requires(0 <= index && index < self.len())]
#    pub fn lookup(&self, index: usize) -> i32 {
#        self.head.lookup(index)
#    }
#
#    #[pure]
#    pub fn len(&self) -> usize {
#        self.head.len()
#    }
#
#    #[ensures(result.len() == 0)]
#    pub fn new() -> Self {
#        List {
#            head: Link::Empty,
#        }
#    }
#
    #[ensures(self.len() == old(self.len()) + 1)]
    #[ensures(self.lookup(0) == elem)]
    #[ensures(forall(|i: usize| (1 <= i && i < self.len()) ==>
                old(self.lookup(i-1)) == self.lookup(i)))]
    pub fn push(&mut self, elem: i32) {
        let new_node = Box::new(Node {
            elem: elem,
            next: replace(&mut self.head, Link::Empty),
        });

        self.head = Link::More(new_node);
    }
}
#
#impl Link {
#    #[pure]
#    #[requires(0 <= index && index < self.len())]
#    pub fn lookup(&self, index: usize) -> i32 {
#        match self {
#            Link::Empty => unreachable!(),
#            Link::More(box node) => {
#                if index == 0 {
#                    node.elem
#                } else {
#                    node.next.lookup(index - 1)
#                }
#            },
#        }
#    }
#
#    #[pure]
#    #[ensures(!self.is_empty() ==> result > 0)]
#    #[ensures(result >= 0)]
#    fn len(&self) -> usize {
#        match self {
#            Link::Empty => 0,
#            Link::More(box node) => 1 + node.next.len(),
#        }
#    }
#
#    #[pure]
#    fn is_empty(&self) -> bool {
#        match self {
#            Link::Empty => true,
#            Link::More(box node) => false,
#        }
#    }
#}
// Prusti: VERIFIES
```
