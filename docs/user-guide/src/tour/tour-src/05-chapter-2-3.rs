#![feature(box_patterns)] // convenience box syntax

/*
    We could verify that the list returned by new() is empty, i.e., is of length 0.
    To this end, we also need to implement a length function for links
*/

// (1) required to enable Prusti's annotations (implemented as Rust macros/attributes)
extern crate prusti_contracts;
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

    // (3) add a method for length without annotations
    // Methods are a special case of function in Rust because of the self argument, 
    // which doesn't have a declared type.
    // There are 3 primary forms that self can take: self, &mut self, and &self
    // We choose &self since computing the length only requires immutable access.
    #[pure] // (4)
    pub fn len(&self) -> usize {
        //0 // only for (3) and (4)
        self.head.len() // (5)
    }

    // (2) add postcondition
    #[ensures(result.len() == 0)]
    pub fn new() -> Self {
        List {
            head: Link::Empty,
        }
    }

}

impl Link {

    // (5) add length method for Links
    #[pure]
    fn len(&self) -> usize {
        0/*
        match self {
            Link::Empty => 0,
            Link::More(box node) => 1 + node.next.len(),
        }
        */
    }

}

fn main() {}
