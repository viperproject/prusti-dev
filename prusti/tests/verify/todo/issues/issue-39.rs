#![feature(nll)]
#![feature(box_patterns)]
#![feature(box_syntax)]

extern crate prusti_contracts;


struct List {
    value: u32,
    next: Option<Box<List>>,
}

#[pure]
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

#[pure]
fn len(head: &List) -> usize {
    match head.next {
        None => 1,
        Some(box ref tail) => 1 + len(tail)
    }
}

#[ensures="len(&result) == old(len(&tail)) + 1"]
#[ensures="lookup(&result, 0) == old(x)"]
#[ensures="forall i: usize :: (0 < i && i < len(&result)) ==> lookup(&result, i) == old(lookup(&tail, i + 1))"]
fn prepend_list(x: u32, tail: List) -> List {
    List {
        value: x,
        next: Some(Box::new(tail)),
    }
}


fn main() {}
