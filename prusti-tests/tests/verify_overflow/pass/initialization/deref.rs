//! Example of reassignment

#![feature(nll)]
#![feature(box_patterns)]
#![feature(box_syntax)]

use prusti_contracts::*;

struct InfiniteList1 {
    next: Box<InfiniteList1>
}

fn consume1(x: InfiniteList1) {}

fn reassignment1(mut x: InfiniteList1) {
    // Consume the only path.
    x = *(*(*(*(*x.next).next).next).next).next;
    consume1(x);
}

struct InfiniteList2 {
    val: u32,
    next: Box<InfiniteList2>
}

fn consume2(x: InfiniteList2) {}

fn reassignment2a(a: InfiniteList2) {
    let mut x = a;
    // Consume one of the paths.
    x = *x.next;
    consume2(x);
}

fn reassignment2b(a: InfiniteList2) {
    let mut x = a;
    // Consume one of the paths.
    x = *(*(*(*(*x.next).next).next).next).next;
    consume2(x);
}

fn main(){}
