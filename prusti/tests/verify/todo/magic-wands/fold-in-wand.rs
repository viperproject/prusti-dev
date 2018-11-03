#![feature(nll)]
#![feature(box_patterns)]

extern crate prusti_contracts;

struct T {
    val: Box<T>
}

fn extract(x: &mut T) -> &mut T {
    match x {
        T { val: box ref mut y } => y
    }
}

fn main() {}
