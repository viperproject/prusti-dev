extern crate prusti_contracts;

struct T(i32);

fn foo(x: &T) {}
fn bar(x: &mut T) {}

fn test (x: T, y: T) {
    let mut x = x;
    let mut y = y;
    let mut r = &x;
    loop {
        foo(r);
        r = &y; //~ ERROR reborrow
        bar(&mut x);
    }
}

fn main(){}
