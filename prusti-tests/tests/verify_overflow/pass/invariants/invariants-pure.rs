// compile-flags: -Penable_type_invariants=true
// ignore-test Unnecessary postcondition on `double` since it's pure.
extern crate prusti_contracts;
use prusti_contracts::*;

// precondition inhale

#[invariant(self.value <= 100)]
#[derive(Clone, Copy)]
struct Percentage {
    value: u8,
}

impl Percentage {
    #[pure]
    fn make_percentage() -> Self {
        Percentage { value: 99 }
    }

    #[pure]
    #[ensures(result <= 200)]
    fn double(&self) -> u8 {
        return self.value * 2
    }
}

fn main() {}
