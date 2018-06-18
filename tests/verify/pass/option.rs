//! Currently unsupported because `Box` and `Option` use a type parameter

#![feature(nll)]
#![feature(box_patterns)]
#![feature(box_syntax)]

extern crate prusti_contracts;

fn main() {
    let x = 123;
    let y = Some(x);
    let z = if let Some(zz) = y { zz } else { panic!() };
    assert!(x == z);
}
