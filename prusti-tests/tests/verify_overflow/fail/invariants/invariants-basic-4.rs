// compile-flags: -Penable_type_invariants=true
extern crate prusti_contracts;
use prusti_contracts::*;

// postcondition (&mut arg) assert

#[invariant(self.value <= 100)]
struct Percentage {
    value: u8,
}

impl Percentage {
    fn incr(&mut self) { //~ ERROR type invariants
        if self.value <= 100 { // mistake
            self.value += 1;
        }
    }
}

fn main() {}
