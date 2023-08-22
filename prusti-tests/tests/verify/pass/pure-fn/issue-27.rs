#![feature(nll)]
#![feature(box_patterns)]

/// See issue #27

use prusti_contracts::*;

use std::borrow::BorrowMut;

struct List {
    next: Option<Box<List>>,
}

#[pure]
fn len(head: &List) -> usize {
    match head.next {
        None => 1,
        Some(box ref tail) => 1
    }
}

#[ensures(len(&result) > 0)]
fn identity(list: List) -> List { list }


fn main() {}
