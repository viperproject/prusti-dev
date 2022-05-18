// compile-flags: -Penable_type_invariants=true
extern crate prusti_contracts;
use prusti_contracts::*;

#[invariant(self.value <= 100)]
struct Percentage<T> {
    value: u8,
    data: T
}

impl <T> Percentage<T> {
    fn incr(&mut self) {
        assert!(self.value <= 100);
        if self.value < 100 {
            self.value += 1;
        }
    }
}

fn main() {}
