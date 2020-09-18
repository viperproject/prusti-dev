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

impl Link {
    #[pure]
    fn is_empty(&self) -> bool {
        match self {
            Link::Empty => true,
            Link::More(box node) => false,
        }
    }
    #[pure]
    #[ensures(!self.is_empty() ==> result > 0)]
    #[ensures(result >= 0)]
    fn len(&self) -> usize {
        match self {
            Link::Empty => 0,
            Link::More(box node) => 1 + node.next.len(),
        }
    }
}

struct Node {
    elem: i32,
    next: Link,
}

#[trusted]
#[requires(src.is_empty())]
#[ensures(old(src.is_empty()) ==> old(dest.len()) == result.len())]
#[ensures(old(src.is_empty()) ==> dest.is_empty())]
fn replace(dest: &mut Link, src: Link) -> Link {
    mem::replace(dest, src)
}

pub fn pop(s: &mut List) {
    replace(&mut s.head, Link::Empty);
}

fn main() {}
