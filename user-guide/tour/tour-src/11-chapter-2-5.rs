#![feature(box_patterns)]
use prusti_contracts::*;

use std::mem;

pub enum TrustedOption {
    Some(i32),
    None,
}

// (3) add implementation for TrustedOption
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

    // (6) add method
    #[pure]
    #[requires(self.is_some())] // (7)
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

    // (1) TODO: What would be sensible specifications for pop()?
    //      a) empty list means we return None
    //      b) non-empty list means we return Some(_)
    //      c) lengths are changed correctly
    //      d) the returned value is the first element of the old list
    //      e) all elements except the first one remain unchanged

    // (2) spec a/b) we could add explicit matches but that would be silly
    #[ensures(old(self.len()) == 0 ==> result.is_none())] // (2) spec a)

    #[ensures(old(self.len()) > 0 ==> result.is_some())]  // (2) spec b)
    // (4) specification c)
    #[ensures(old(self.len()) == 0 ==> self.len() == 0)]  // (4) empty lists remain empty
    #[ensures(old(self.len()) > 0 ==> self.len() == old(self.len()-1))] // (4) non-empty lists are 1 smaller
    // (5) specification d)
    #[ensures(old(self.len()) > 0 ==> result.peek() == old(self.lookup(0)))] // (5)
    // (6) specification e)
    #[ensures(old(self.len()) > 0 ==> // (6)
    forall(|i: usize| (0 <= i && i < self.len()) ==> // (6)
        old(self.lookup(i+1)) == self.lookup(i)))] // (6)
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
