# New 

> **Recommended reading:** 
> [2.2: New](https://rust-unofficial.github.io/too-many-lists/first-new.html), 
> [2.3: Ownership 101](https://rust-unofficial.github.io/too-many-lists/first-ownership.html)
> 
> How to associate code with a type through `impl` blocks; 
> writing simple static functions;
> Rust's ownership system.

## Implementing New

We first provide a static function to create empty lists:

```rust,noplaypen
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
{{#include tour-src/04-chapter-2-2.rs:15:22}}
// Prusti: VERIFIES
```

## A First Specification

What would be a sensible first specification for `new()`?
We could attempt to verify the list returned by `new()` is always empty.
In other words, the length of the returned list is always zero.
To express this property, we first implement a length method for lists which
itself calls an auxiliary length method implemented for `Link`.
For simplicity, we will not actually compute the length of a `Link` yet.
Rather, we will just always return 0.

```rust,noplaypen
#![feature(box_patterns)] // convenience notation for boxes
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
    pub fn len(&self) -> usize {
        self.head.len()
    }
#
#    pub fn new() -> Self {
#        List {
#            head: Link::Empty,
#        }
#    }
}

impl Link {
    fn len(&self) -> usize {
        0
    }
}
// Prusti: VERIFIES
```

Now that we have implemented a method for computing the length of a list, we can
write our first specification for `new()`: the returned list should always have length
zero.
That is, we attach the [postcondition](../verify/prepost.md)
`result.len() == 0` to the function `new()`:

```rust,noplaypen
#//uncomment: #![feature(box_patterns)]
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
#impl List {
#    pub fn len(&self) -> usize {
#        self.head.len()
#    }
#
    #[ensures(result.len() == 0)]
    pub fn new() -> Self {
        List {
            head: Link::Empty
        }
    }
#}
#
#impl Link {
#    fn len(&self) -> usize {
#        0
#    }
#}
```

Unfortunately, Prusti—or rather: the Rust compiler—will complain about
the postcondition:

```
error: cannot find attribute `ensures` in this scope
  --> list.rs:39:7
   |
39 |     #[ensures(result.len() == 0)]    
   |       ^^^^^^^
```

Prusti's specifications consist of Rust
[macros and attributes](https://doc.rust-lang.org/reference/procedural-macros.html)
that are defined in a separate crate called `prusti_contracts`.
Before we can use these specifications, we need to make the path to these
macros and attributes visible:

```rust,noplaypen
#//uncomment: #![feature(box_patterns)]
use prusti_contracts::*; 

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
#    pub fn len(&self) -> usize {
#        self.head.len()
#    }
#
    #[ensures(result.len() == 0)]
    pub fn new() -> Self {
        List {
            head: Link::Empty
        }
    }
}
#
#impl Link {
#    fn len(&self) -> usize {
#        0
#    }
#}
```

Declaring that we use the `prusti_contracts` crate removes the compiler error but
leads to a new error. This time it is an error raised by Prusti:

```
error: [Prusti: invalid specification] use of impure function "List::len" in pure code is not allowed
  --> list.rs:34:15
   |
34 |     #[ensures(result.len() == 0)]    
   | 
```

Prusti complains about our use of the method `len()` in a postcondition because the
[specification syntax](../syntax.md) only admits calling so-called
[pure functions](../verify/pure.md), that is, functions that are deterministic,
have no side effects, and always terminate.

While our implementation of `len()` clearly satisfies all of the above properties,
Prusti requires us to explicitly mark a function with the `#[pure]` attribute
before it considers a function pure.
After adding the `#[pure]` attribute to our `List::len()` method, it is allowed to
appear in Prusti specifications:

```rust,noplaypen
#//uncomment: #![feature(box_patterns)]
#extern crate prusti_contracts;
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
    #[pure]
    pub fn len(&self) -> usize {
        self.head.len()
    }
#
#    #[ensures(result.len() == 0)]
#    pub fn new() -> Self {
#        List {
#            head: Link::Empty,
#        }
#    }
}
#
#impl Link {
#    fn len(&self) -> usize {
#        0
#    }
#}
```

However, Prusti still won't verify! It produces the same error but now it refers
to the *body* of `len()`:

```
error: [Prusti: invalid specification] use of impure function "Link::len" in pure code is not allowed
  --> list.rs:30:9
   |
30 |         self.head.len() // (5)
   |         ^^^^
```

Whenever we add the attribute `#[pure]` to a function, Prusti will check whether that
function is indeed deterministic and side-effect free
(notice that termination is *not* checked); otherwise, it complains.
In this case, Prusti complains because we call an impure function,
namely `Link::len()`, within the body of the pure function `List::len()`.

To fix this issue, it suffices to mark `Link::len()` as pure as well.

```rust,noplaypen
#//uncomment: #![feature(box_patterns)]
#extern crate prusti_contracts;
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
#}
#
impl Link {
    #[pure]
    fn len(&self) -> usize {
        0
    }
}
#
# fn main() {} // in case Prusti is used via command line
#
// Prusti: VERIFIES
```

```
$ prusti-rustc list.rs
// ...
Successful verification of 4 items
```

Prusti now manages to verify that `new()` always returns
a list for which the method `len()` returns 0. (notice
this is hardly surprising since `len()` ultimately always returns 0 but we will change
this soon.)

## Full code listing

Before we continue, we provide the full code implented in this chapter.
It should successfully verify with Prusti and we will further extend it throughout
the next four chapters.

```rust,noplaypen
#![feature(box_patterns)]
use prusti_contracts::*;

pub struct List {
    head: Link,
}

enum Link {
    Empty,
    More(Box<Node>),
}

struct Node {
    elem: i32,
    next: Link,
}

impl List {
    #[pure]
    pub fn len(&self) -> usize {
        self.head.len()
    }

    #[ensures(result.len() == 0)]
    pub fn new() -> Self {
        List {
            head: Link::Empty,
        }
    }
}

impl Link {
    #[pure]
    fn len(&self) -> usize {
        0
    }
}

fn main() {} // in case Prusti is used via command line

// Prusti: VERIFIES
```
