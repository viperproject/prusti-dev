#![feature(nll)]
#![feature(box_patterns)]
#![feature(box_syntax)]

extern crate prusti_contracts;

use std::borrow::BorrowMut;

struct List {
    value: u32,
    next: Option<Box<List>>,
}

// Pure function
fn lookup(head: &List, index: usize) -> u32 {
    unimplemented!()
}

// Pure function
fn len(head: &List) -> usize {
    unimplemented!()
}

// Returns the last node of the linked list. Recursive implementation.
#[ensures="result.next.is_none()"]
#[ensures="result.value == old(lookup(head, len(head) - 1))"]
/*#[ensures="
    promise/at_expiry<'a>(
        forall i: usize :: {} (0 <= i && i < old(len(head)) - 1) ==> lookup(head, i) == old(lookup(head, i)) &&
        forall i: usize :: {} (0 <= i && i < now(len(result))) ==> lookup(head, old(len(head)) - 1 + i) == now(lookup(result, i)) &&
        len(head) == old(len(head)) - 1 + now(len(result))
    )
"]*/
fn recursive_get_last(head: &mut List) -> &mut List {
    match head.next {
        None => head,
        Some(box ref mut next) => recursive_get_last(next)
    }
}

// Returns the last node of the linked list. Iterative implementation.
#[ensures="result.next.is_none()"]
#[ensures="result.value == old(lookup(head, len(head) - 1))"]
/*#[ensures="
    promise/at_expiry<'a>(
        forall i: usize :: {} (0 <= i && i < old(len(head)) - 1) ==> lookup(head, i) == old(lookup(head, i)) &&
        forall i: usize :: {} (0 <= i && i < now(len(result))) ==> lookup(head, old(len(head)) - 1 + i) == now(lookup(result, i)) &&
        len(head) == old(len(head)) - 1 + now(len(result))
    )
"]*/
fn iterative_get_last<'a>(head: &'a mut List) -> &'a mut List {
    let mut curr = head;
    while curr.next.is_some() {
        curr = curr.next.as_mut().unwrap().borrow_mut();
    }
    curr
}

// Appends a value at the end of a linked list
#[ensures="len(head) == old(len(head)) + 1"]
#[ensures="value == lookup(head, len(head) - 1)"]
#[ensures="forall i: usize :: {true} (0 <= i && i < old(len(head))) ==> lookup(head, i) == old(lookup(head, i))"]
#[ensures="forall i: usize :: {true} i == 0 ==> i != 1"]
fn append(head: &mut List, value: u32) {
    let last = iterative_get_last(head);
    assert!(last.next.is_none());
    last.next = Some(box List {
        next: None,
        value: value,
    });
}

fn main() {}
