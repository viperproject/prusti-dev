extern crate prusti_contracts;
use prusti_contracts::*;

// precondition assert

#[invariant(self.value <= 100)]
struct Percentage {
    value: u8,
}

impl Percentage {
    fn incr(&mut self) {
        if self.value < 100 {
            self.value += 1;
        }
    }
}

//#[requires(x <= 100)]
fn test(x: u8) {
    let mut perc = Percentage { value: x };
    perc.incr(); //~ ERROR precondition might not hold
}

fn main() {}
