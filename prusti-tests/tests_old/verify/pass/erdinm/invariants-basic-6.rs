use prusti_contracts::*;

// postcondition (result) assert

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

fn main() {}
