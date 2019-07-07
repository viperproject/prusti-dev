extern crate prusti_contracts;

// precondition inhale

//#[invariant="self.value <= 100"]
struct Percentage {
    value: u8,
}

impl Percentage {
    fn incr(&mut self) {
        assert!(self.value <= 100); //~ ERROR the asserted expression might not hold
        if self.value < 100 {
            self.value += 1;
        }
    }
}

fn main() {}
