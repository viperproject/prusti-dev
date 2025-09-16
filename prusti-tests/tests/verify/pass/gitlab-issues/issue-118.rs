#![feature(nll)]
#![feature(box_patterns)]

use prusti_contracts::*;

struct List {
    next: Box<List>,
}

fn consume(head: &mut List) {
}

fn recursive(head: &mut List, b: bool) {
    let x = if b {
        let box ref mut int_next = head.next;
        int_next
    } else {
        head
    };
    consume(x);
}

fn main() {}
