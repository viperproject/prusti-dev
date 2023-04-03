#![feature(box_patterns)]

use std::borrow::BorrowMut;

struct List {
    value: u32,
    next: Option<Box<List>>,
}

fn lookup(head: &List, index: usize) -> u32 {
    let result;
    if index == 0 {
        result = head.value
    } else {
        match head.next {
            Some(box ref tail) => {
                result = lookup(tail, index - 1);
            }
            None => {
                unreachable!();
            }
        }
    }
    result
}
