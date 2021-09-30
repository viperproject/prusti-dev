extern crate prusti_contracts;
use prusti_contracts::*;

// postcondition (result) inhale

#[invariant(self.value <= 100)]
struct Percentage {
    value: u8,
}

impl Percentage {
    #[requires(value <= 100)]
    fn new(value: u8) -> Self {
        Percentage {
            value: value,
        }
    }
}

#[requires(x <= 100)]
fn test(x: u8) {
    let perc = Percentage::new(x);
    assert!(perc.value <= 100);
}

fn main() {}
