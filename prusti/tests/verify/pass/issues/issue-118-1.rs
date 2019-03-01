#![feature(nll)]
#![feature(box_patterns)]
#![feature(box_syntax)]

extern crate prusti_contracts;

struct List {
    value: u32,
    next: Option<Box<List>>,
}

fn recursive_get_last(head: &mut List) -> &mut u32 {
    match head.next {
        None => &mut head.value,
        Some(box ref mut next_ref) => recursive_get_last(next_ref)
    }
}

fn main() {}
