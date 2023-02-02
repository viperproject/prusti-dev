#![feature(box_patterns)]
use prusti_contracts::*;

use std::mem;

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

// (3) add a trusted wrapper such that we can come up with a spec
//     such wrappers are common for frontends when dealing with functions
//     that use, for example, the operating system or unsafe/too complicated code
#[trusted]
// (4) Wait wait, this spec is not checked and looks very dangerous!
// We should at least requiree that it is only called with an empty link
// We can then also ensure that the replaced list will be that empty link
#[requires(src.is_empty())] // (4) also requires defining is_empty() below
#[ensures(dest.is_empty())] // (4)
#[ensures(old(dest.len()) == result.len())] // (3)
fn replace(dest: &mut Link, src: Link) -> Link {
    mem::replace(dest, src)
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

    // (1) Let's collect some possible specs:
    //      a) The length of the list increases by one (3): check
    //      b) The first element is the pushed one
    //      c) All other elements have not been changed
    #[ensures(self.len() == old(self.len()) + 1)] // (2) Why does this not hold? mem::replace has no spec!
    pub fn push(&mut self, elem: i32) {
        let new_node = Box::new(Node {
            elem: elem,
            // (1) next: mem::replace(&mut self.head, Link::Empty),
            next: replace(&mut self.head, Link::Empty), // (3)
        });

        self.head = Link::More(new_node);
    }
}

impl Link {

    #[pure]
    fn len(&self) -> usize {
        match self {
            Link::Empty => 0,
            Link::More(box node) => 1 + node.next.len(),
        }
    }

    // (4)
    #[pure]
    fn is_empty(&self) -> bool {
        match self {
            Link::Empty => true,
            Link::More(box node) => false,
        }
    }

}
