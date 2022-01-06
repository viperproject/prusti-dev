#![feature(box_patterns)]

fn foo<T>(x: T) {}

fn main() {
    let mut x = Box::new(123);
    let y = &x;
    foo(y);
    // `y` should expire here
    let z = &mut x;
    foo(z);
}
