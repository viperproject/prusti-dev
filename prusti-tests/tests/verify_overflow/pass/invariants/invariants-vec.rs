extern crate prusti_contracts;
use prusti_contracts::*;

#[invariant(self.value <= 100)]
#[derive(Clone, Copy)]
struct Percentage {
    value: u8,
}

fn get_first<T: Copy>(p: Vec<T>) -> T {
    p[0]
}

#[ensures(result.value <= 100)]
fn get_first_percentage(p: Vec<Percentage>) -> Percentage {
    get_first(p)
}

fn main() {}
