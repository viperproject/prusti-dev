#![allow(dropping_copy_types)]

#[analyzer::run]
fn main() {
    let x = [1, 2, 3];
    drop(x);
    let y = [Box::new(4)];
    drop(y);
}
