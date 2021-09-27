extern crate prusti_contracts;
use prusti_contracts::*;

// postcondition (&mut arg) assert

#[invariant(self.value <= 100)]
struct Percentage {
    value: u8,
}

impl Percentage {
    fn incr(&mut self) {
        if self.value < 100 {
            self.value += 1;
        }
    } // trivial test case
}

fn main() {}
