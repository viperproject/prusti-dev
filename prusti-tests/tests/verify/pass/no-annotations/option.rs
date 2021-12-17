//! Currently unsupported because `Box` and `Option` use a type parameter

#![feature(box_patterns)]
#![feature(box_syntax)]

fn main() {
    let x = 123;
    let y = Some(x);
    let z = if let Some(zz) = y { zz } else { panic!() };
    assert!(x == z);
}
