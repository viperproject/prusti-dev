//! Example of reassignment

#![feature(box_patterns)]

struct InfiniteList {
    val: i32,
    next: Box<InfiniteList>
}

fn consume(x: InfiniteList) {}

fn reassignment(a: InfiniteList) {
    let mut x = a;

    // Reassignment
    x = *(*(*(*(*x.next).next).next).next).next;

    consume(x);
}

fn main(){}
