extern crate prusti_contracts;

// test-ignore: Not yet supported (entered unreachable code: Borrow restores rvalue const true)

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
