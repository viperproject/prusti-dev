extern crate prusti_contracts;

fn test_borrow_in_guard() {
    let mut x: &mut Box<i32>;
    let mut y = Box::new(123);
    while {
        x = &mut y;
        true
    } {
        drop(x);
    }
}

fn main() {}
