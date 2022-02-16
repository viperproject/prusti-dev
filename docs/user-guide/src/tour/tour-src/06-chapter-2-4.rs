#![feature(box_patterns)]
use prusti_contracts::*;

use std::mem; // (4)

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

/*
    Chapter 2.4 - Push

    So let's write pushing a value onto a list. 
    push mutates the list, so we'll want to take &mut self
*/

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

    /*
    // (2) compile this before proceeding
    pub fn push(&mut self, elem: i32) {
        
        let new_node = Node {
            elem: elem,
            next: self.head, // this should be the old list
                             // this does not work:
                             // once the self borrow expired, the old List would only be
                             // partially initialized because we moved self.head
                             // and that cannot be copied.
        };
    }
    */

    /* 
    // (3) What if we put something back? Namely, the node that we're creating.
    // Rust does not accept this for exception safety.
    pub fn push(&mut self, elem: i32) {
        let new_node = Box::new(Node {
            elem: elem,
            next: self.head,
        });
    
        self.head = Link::More(new_node);
    }
    */

    // (4) A correct solution would be to first steal a value out of a borrow and
    //     replace it with another one
    //     We use std::mem:replace for that (add use directive at the top)
    pub fn push(&mut self, elem: i32) {
        let new_node = Box::new(Node {
            elem: elem,
            next: mem::replace(&mut self.head, Link::Empty),
        });
    
        self.head = Link::More(new_node);
    }

    // (5) this verifies!
    // TODO: What would be reasonable first specs for push?
}

impl Link {

    #[pure]
    fn len(&self) -> usize {
        match self {
            Link::Empty => 0,
            Link::More(box node) => 1 + node.next.len(),
        }
    }

}
