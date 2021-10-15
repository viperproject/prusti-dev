extern crate prusti_contracts;
use prusti_contracts::*;

#[invariant(self.value <= 100)]
struct Percentage {
    value: u8,
}

#[ensures(result <= 100)]
fn get_first_percentage(p: Vec<Percentage>) -> u8 {
    p[0].value
}

fn main() {}
