use prusti_contracts::*;

#[requires(x > 123)]
fn test(x: i32, unused: usize) {
    assert!(x > 123);
}

fn main() {
    test(1, 0);
}
