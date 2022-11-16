#![feature(nll)]
#![feature(box_patterns)]
#![feature(box_syntax)]
#![feature(never_type)]
#![allow(unconditional_recursion)]

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

fn diverging() -> ! {
    diverging()
}

fn prepend_list(x: u32, tail: List, check: bool) -> List {
    let mut result = List {
        value: x,
        next: Some(Box::new(tail)),
    };
    if check {
        assert!(lookup(&mut result, 0) == x);
        diverging();
    } else {
        result
    }
}


fn main() {}
