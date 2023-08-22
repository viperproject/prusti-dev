use prusti_contracts::*;

#[pure]
#[requires(curr >= 0)]
fn a(curr: i32) -> bool{
    b(curr)
}

#[pure]
#[requires(curr >= 0)]
fn b(curr: i32) -> bool {
    if curr == 0 {
        return true;
    }
    else{
        a(curr - 1)
    }
}

fn test() {
    assert!(b(0));
    assert!(a(0));
    assert!(b(1));
    assert!(a(1));
    assert!(b(2));
    assert!(a(2));
    assert!(b(3));
    assert!(a(3));
    assert!(b(4));
    assert!(a(4));
    assert!(b(5));
    assert!(a(5));
}

fn main() {}
