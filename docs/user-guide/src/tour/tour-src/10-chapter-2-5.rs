/*
    Chapter 2.5 Pop

    Like push, pop wants to mutate the list. 
    Unlike push, we actually want to return something. 
    But pop also has to deal with a tricky corner case: what if the list is empty?
    To represent this case, we introduce an Option type.
    (Option is actually in the standard library but we write our own to assign specs to functions)
*/

#![feature(box_patterns)]
use prusti_contracts::*;

use std::mem;

// (1) alternative would be to introduce trusted functions again...
pub enum TrustedOption {
    Some(i32),
    None,
}

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
#[ensures(forall(|i: usize| (0 <= i && i < result.len()) ==> 
                old(dest.lookup(i)) == result.lookup(i)))] 
fn replace(dest: &mut Link, src: Link) -> Link {
    mem::replace(dest, src)
}


impl List {

    #[pure]
    pub fn len(&self) -> usize {
        self.head.len()
    }

    #[pure]
    #[requires(0 <= index && index < self.len())]
    pub fn lookup(&self, index: usize) -> i32 {
        self.head.lookup(index)
    }

    #[ensures(result.len() == 0)]
    pub fn new() -> Self {
        List {
            head: Link::Empty,
        }
    }

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

    // (6) TODO: What would be sensible specifications for pop()?
    // (2): introduce function below
    pub fn pop(&mut self) -> TrustedOption {
        // match self.head { // (2) move out of borrow
        //match &self.head { // (3) use shared reborrow
        match replace(&mut self.head, Link::Empty) { // (5)
            Link::Empty => {
                TrustedOption::None // (4)
            }
            Link::More(node) => {
                self.head = node.next; // (4) cannot assign, we just borrowed self.head!
                TrustedOption::Some(node.elem) // (4)
            }
        }
        // unimplemented!() // (2), remove at (4)
    }
}

impl Link {

    #[pure]
    #[ensures(!self.is_empty() ==> result > 0)]
    #[ensures(result >= 0)]
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

    #[pure]
    #[requires(0 <= index && index < self.len())]
    pub fn lookup(&self, index: usize) -> i32 {
        match self {
            Link::Empty => unreachable!(),
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
