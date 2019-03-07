#![feature(nll)]
#![feature(box_patterns)]
#![feature(box_syntax)]

extern crate prusti_contracts;

use std::borrow::BorrowMut;

struct List {
    value: u32,
    next: Option<Box<List>>,
}

#[pure]
fn lookup(head: &List, index: isize) -> u32 {
    if index == 0 {
        head.value
    } else {
        match head.next {
            Some(box ref tail) => lookup(tail, index - 1),
            None => unreachable!() //~ ERROR might be reachable
        }
    }
}

#[pure]
fn len(head: &List) -> isize {
    match head.next {
        None => 1,
        Some(box ref tail) => 1 + len(tail)
    }
}

#[ensures="len(&result) == old(len(&tail)) + 1"] //~ ERROR
#[ensures="lookup(&result, 0) == old(x)"]
#[ensures="if len(&result) >= 2 { old(lookup(&tail, 0)) == lookup(&result, 1) } else { true }"]
#[ensures="forall i: isize :: (0 <= i && i < old(len(&tail))) ==> old(lookup(&tail, i)) == lookup(&result, i)"]
#[ensures="forall i: isize :: (0 <= i && i < old(len(&tail))) ==> i * 2 == i + i"]
fn prepend_list(x: u32, tail: List) -> List {
    List {
        value: x,
        next: Some(Box::new(tail)),
    }
}

fn main() {}
