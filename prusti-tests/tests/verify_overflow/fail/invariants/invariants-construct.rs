extern crate prusti_contracts;
use prusti_contracts::*;

#[invariant(self.value <= 100)]
struct Percentage {
    value: u8,
}

fn make_percentage() -> Percentage { //~ ERROR type invariants
    Percentage { value: 101 }
}

fn main() {}
