#![feature(nll)]
#![feature(box_patterns)]
#![feature(box_syntax)]

extern crate prusti_contracts;

use std::borrow::BorrowMut;

struct List {
    value: u32,
    next: Option<Box<List>>,
}

/// Returns the last List of the linked head. Recursive implementation.
fn recursive_get_last(list: &mut List) -> &mut List {
    match list.next {
        None => list,
        Some(box ref mut next) => recursive_get_last(next)
    }
}

/// Returns the last List of the linked head. Iterative implementation.
fn iterative_get_last(head: &mut List) -> &mut List {
    let mut curr = head;
    while curr.next.is_some() {
        curr = curr.next.as_mut().unwrap().borrow_mut();
    }
    curr
}

/// Appends a value at the end of a linked head
fn append(head: &mut List, value: u32) {
    let last = iterative_get_last(head);
    assert!(last.next.is_none());
    last.next = Some(box List {
        next: None,
        value: value,
    });
}

fn main() {}
