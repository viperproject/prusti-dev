#![feature(nll)]
#![feature(box_patterns)]

use prusti_contracts::*;

use std::borrow::BorrowMut;

struct List {
    value: u32,
    next: Option<Box<List>>,
}

#[pure]
#[ensures(result > 0)]
fn len(head: &List) -> usize {
    match head.next {
        None => 1,
        Some(box ref tail) => 1 + len(tail)
    }
}

#[pure]
#[requires(0 <= index && index < len(head))]
fn lookup(head: &List, index: usize) -> u32 {
    if index == 0 {
        head.value
    } else {
        match head.next {
            Some(box ref tail) => lookup(tail, index - 1),
            None => unreachable!()
        }
    }
}

#[ensures(len(&result) == old(len(&tail)) + 1)]
#[ensures(lookup(&result, 0) == old(x))]
#[ensures(if len(&result) >= 2 { old(lookup(&tail, 0)) == lookup(&result, 1) } else { true })]
#[ensures(forall(|i: usize| (0 <= i && i < old(len(&tail))) ==> old(lookup(&tail, i)) == lookup(&result, i + 1)))]
#[ensures(forall(|i: usize| (0 <= i && i < old(len(&tail))) ==> i * 2 == i + i))]
fn prepend_list(x: u32, tail: List) -> List {
    List {
        value: x,
        next: Some(Box::new(tail)),
    }
}

fn main() {}
