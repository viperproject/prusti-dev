extern crate prusti_contracts;

// postcondition (&mut arg) assert

#[invariant="self.value <= 100"]
struct Percentage {
    value: u8,
}

impl Percentage {
    fn incr(&mut self) { //~ ERROR postcondition might not hold
        if self.value <= 100 { // mistake
            self.value += 1;
        }
    }
}

fn main() {}
