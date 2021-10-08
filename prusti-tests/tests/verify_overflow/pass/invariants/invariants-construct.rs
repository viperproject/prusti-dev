extern crate prusti_contracts;
use prusti_contracts::*;

#[invariant(self.value <= 100)]
struct Percentage {
    value: u8,
}

fn make_percentage() -> Percentage {
    Percentage { value: 99 }
}

fn main() {}
