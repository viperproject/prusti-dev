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

#[ensures(len(&result) > 0)]
#[ensures(old(len(&list)) == len(&result))]
#[ensures(if len(&result) > 0 { old(lookup(&list, 0)) == lookup(&result, 0) } else { true })]
fn identity(list: List) -> List { list }


#[ensures(len(&result) == 1)]
#[ensures(lookup(&result, 0) == old(x))]
fn build_list_1(x: u32) -> List {
    List {
        value: x,
        next: None,
    }
}

#[ensures(len(&result) == 2)]
#[ensures(lookup(&result, 0) == old(x))]
#[ensures(lookup(&result, 1) == old(y))]
fn build_list_2(x: u32, y: u32) -> List {
    let tail = build_list_1(y);
    List {
        value: x,
        next: Some(Box::new(tail)),
    }
}

#[ensures(len(&result) == old(len(&tail)) + 1)]
#[ensures(lookup(&result, 0) == old(x))]
#[ensures(forall(|i: usize| (i > 0 && i < len(&result)) ==> lookup(&result, i) == old(lookup(&tail, i - 1))))]
fn prepend_list(x: u32, tail: List) -> List {
    List {
        value: x,
        next: Some(Box::new(tail)),
    }
}


fn main() {}
