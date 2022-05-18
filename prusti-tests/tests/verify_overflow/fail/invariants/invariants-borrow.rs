// compile-flags: -Penable_type_invariants=true
extern crate prusti_contracts;
use prusti_contracts::*;

#[invariant(self.value <= 100)]
struct Percentage {
    value: u8,
}

fn make_percentage() -> Percentage { //~ ERROR type invariants
    let mut p = Percentage { value: 100 };
    double(&mut p.value);
    p
}

#[requires(*x <= 100)]
fn double(x: &mut u8) {
  *x = *x * 2;
}

fn main() {}
