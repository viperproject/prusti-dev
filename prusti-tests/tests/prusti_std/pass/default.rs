use prusti_contracts::*;

fn main() {
    let default: (i32, i32) = Default::default();
    assert!(default.0 == 0);
    assert!(default.1 == 0);
}
