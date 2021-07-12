#![feature(type_ascription)]

mod swap;

fn main() {
    let mut x = 5;
    let mut y = 42;

    std::mem::swap(&mut x, &mut y);

    assert!(42 == x);
    assert!(5 == y);
}
