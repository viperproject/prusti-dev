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

#[trusted]
#[requires(src.is_empty())]
#[ensures(dest.is_empty())]
#[ensures(old(dest.len()) == result.len())]
fn replace(dest: &mut Link, src: Link) -> Link {
    mem::replace(dest, src)
}


impl List {

    #[pure]
    pub fn len(&self) -> usize {
        self.head.len()
    }

    // (3)
    #[pure]
    #[requires(0 <= index && index < self.len())] // (9)
    pub fn lookup(&self, index: usize) -> i32 {
        self.head.lookup(index)
    }

    #[ensures(result.len() == 0)]
    pub fn new() -> Self {
        List {
            head: Link::Empty,
        }
    }

    // (1) Let's collect some possible specs:
    //      a) The length of the list increases by one: check
    //      b) The first element is the pushed one
    //      c) All other elements have not been changed
    #[ensures(self.len() == old(self.len()) + 1)] 
    #[ensures(self.lookup(0) == elem)] // (2) express property b)
    pub fn push(&mut self, elem: i32) {
        let new_node = Box::new(Node {
            elem: elem,
            next: replace(&mut self.head, Link::Empty), 
        });

        self.head = Link::More(new_node);
    }
}

impl Link {

    #[pure]
    #[ensures(!self.is_empty() ==> result > 0)] // (7)
    #[ensures(result >= 0)] // (8)
    fn len(&self) -> usize {
        match self {
            Link::Empty => 0,
            Link::More(box node) => 1 + node.next.len(),
        }
    }

    #[pure]
    fn is_empty(&self) -> bool {
        match self {
            Link::Empty => true,
            Link::More(box node) => false,
        }
    }

    // (4)
    #[pure]
    #[requires(0 <= index && index < self.len())] // (6) no fix as there's no 
                                                  // relation between being empty and length 0
    pub fn lookup(&self, index: usize) -> i32 {
        match self {
            Link::Empty => unreachable!(), // (5) reachable because list might be empty
            Link::More(box node) => {
                if index == 0 {
                    node.elem
                } else {
                    node.next.lookup(index - 1)
                }
            }
        }
    }

}
