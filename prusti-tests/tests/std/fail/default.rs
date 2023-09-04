use prusti_contracts::*;
use prusti_std;

fn main() {}

fn element0() {
    let default: (Special, i32) = Default::default();
    assert!(default.0.value == 0); //~ ERROR: the asserted expression might not
}

fn element1() {
    let default: (Special, i32) = Default::default();
    assert!(default.1 == 0); //~ ERROR: the asserted expression might not hold
}

fn special_value() {
    let default: Special = Default::default();
    assert!(default.value == 0); //~ ERROR: the asserted expression might not hold
}

// not Copy => Default not pure
#[derive(Default)]
struct Special {
    value: i32,
}
