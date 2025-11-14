use prusti_contracts::*;

struct Bar();

impl Bar {
    const CONST: i32 = i32::MAX;
}

fn main() {
    prusti_assert!(Bar::CONST == i32::MAX);
}
