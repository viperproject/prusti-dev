/*
    Chapter 2.6 - Testing
    Alright, so we've got push and pop written, now we can actually test out our stack! 
    Rust and cargo support testing as a first-class feature, 
    so this will be super easy. 
    All we have to do is write a function, and annotate it with #[test].
*/

#![feature(box_patterns)]
use prusti_contracts::*;

use std::mem;

pub enum TrustedOption {
    Some(i32),
    None,
}

impl TrustedOption {

    #[pure]
    pub fn is_none(&self) -> bool {
        match self {
            TrustedOption::Some(_) => false,
            TrustedOption::None => true,
        }
    }

    #[pure]
    pub fn is_some(&self) -> bool {
        !self.is_none()
    }

    #[pure]
    #[requires(self.is_some())]
    pub fn peek(&self) -> i32 {
        match self {
            TrustedOption::Some(val) => *val,
            TrustedOption::None => unreachable!(),
        }
    }

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
            head: Link::Empty
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

    #[ensures(old(self.len()) == 0 ==> result.is_none())]
    #[ensures(old(self.len()) > 0 ==> result.is_some())]
    #[ensures(old(self.len()) == 0 ==> self.len() == 0)]
    #[ensures(old(self.len()) > 0 ==> self.len() == old(self.len()-1))]
    #[ensures(old(self.len()) > 0 ==> result.peek() == old(self.lookup(0)))]
    #[ensures(old(self.len()) > 0 ==>
    forall(|i: usize| (0 <= i && i < self.len()) ==>
        old(self.lookup(i+1)) == self.lookup(i)))]
    pub fn pop(&mut self) -> TrustedOption {
        match replace(&mut self.head, Link::Empty) {
            Link::Empty => {
                TrustedOption::None
            }
            Link::More(node) => {
                self.head = node.next;
                TrustedOption::Some(node.elem)
            }
        }
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


// (1)
pub mod test {
    use super::{List, TrustedOption};

    pub fn basics() {
        let mut list = List::new();

        // (1) Check empty list behaves right
        assert!(list.pop().is_none());

        // (2) Populate list
        list.push(1);
        list.push(2);
        list.push(3);

        // (2) Check normal removal
        match list.pop() {
            TrustedOption::Some(val) => assert!(val == 3),
            _ => unreachable!(),
        }
        match list.pop() {
            TrustedOption::Some(val) => assert!(val == 2),
            _ => unreachable!(),
        }

        // (3) Push some more just to make sure nothing's corrupted
        list.push(4);
        list.push(5);

        // (3) Check normal removal
        match list.pop() {
            TrustedOption::Some(val) => assert!(val == 5),
            _ => unreachable!(),
        }
        match list.pop() {
            TrustedOption::Some(val) => assert!(val == 4),
            _ => unreachable!(),
        }

        // (4) Check exhaustion
        match list.pop() {
            TrustedOption::Some(val) => assert!(val == 1),
            _ => unreachable!(),
        }
        assert!(list.pop().is_none());
    }
}
