// compile-flags: -Penable_type_invariants=true
extern crate prusti_contracts;
use prusti_contracts::*;

// precondition inhale

#[invariant(self.value <= 100)]
struct Percentage {
    value: u8,
}

impl Percentage {

    fn incr_loop(&mut self) {
        while self.value < 100 {
            body_invariant!(self.value < 100);
            self.value += 1;
        }
    }
}

fn inspect(percentage: &Percentage) {

}

#[requires(percentage.value <= 95)]
fn call_inside_loop(percentage: &mut Percentage) {
    let mut i = 0;
    while i < 5 {
        body_invariant!(i < 5);
        body_invariant!(percentage.value == old(percentage.value) + i);
        percentage.value += 1;
        inspect(percentage);
        i += 1;
    }
}

fn main() {}
