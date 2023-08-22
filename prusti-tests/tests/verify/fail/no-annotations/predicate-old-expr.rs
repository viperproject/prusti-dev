#![feature(nll)]
#![feature(box_patterns)]

use std::borrow::BorrowMut;

struct List {
    value: u32,
    next: Option<Box<List>>,
}

fn lookup(head: &List, index: usize) -> u32 {
    if index == 0 {
        head.value
    } else {
        match head.next {
            Some(box ref tail) => lookup(tail, index - 1),
            None => unreachable!() //~ ERROR unreachable!(..) statement might be reachable
        }
    }
}

fn main() {}
