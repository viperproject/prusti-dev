#![feature(nll)]
#![feature(box_patterns)]
#![feature(box_syntax)]

extern crate prusti_contracts;

use std::borrow::BorrowMut;

struct List {
    value: u32,
    next: Option<Box<List>>,
}

fn construct_list() -> List {
    unimplemented!()
}

fn iterative_get_last<'a>(head: &'a mut List) -> &'a mut List {
    let mut curr = head;
    let mut cont = curr.next.is_some();
    while cont {
        curr = curr.next.as_mut().unwrap().borrow_mut();
        cont = curr.next.is_some();
    }
    curr
}

fn iterative_get_last2() {
    let mut list = construct_list();
    let mut head = &mut list;
    let mut curr = head;
    let mut cont = curr.next.is_some();
    while cont {
        curr = curr.next.as_mut().unwrap().borrow_mut();
        cont = curr.next.is_some();
    }
    iterative_get_last(curr);
}

fn main() {}
