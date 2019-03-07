extern crate prusti_contracts;

#[invariant="self.value <= 100"]
struct Percentage {
    value: u8,
}

impl Percentage {
    #[requires="value <= 100"]
    fn new(value: u8) -> Self {
        Percentage {
            value: value,
        }
    }

    #[requires="value <= 101"] // mistake
    fn new_fail(value: u8) -> Self { //~ ERROR type invariants
        Percentage {
            value: value,
        }
    }

    fn incr(&mut self) {
        assert!(self.value <= 100);
        if self.value < 100 {
            self.value += 1;
        }
    }

    fn incr_fail1(&mut self) {
        assert!(self.value <= 99); //~ ERROR assert!(..) statement might not hold
        if self.value < 100 {
            self.value += 1;
        }
    }

    fn incr_fail2(&mut self) { //~ ERROR type invariants
        if self.value <= 100 { // mistake
            self.value += 1;
        }
    }
}

#[requires="x <= 100"]
fn test1(x: u8) {
    let perc = Percentage::new(x);
    assert!(perc.value <= 100);
}

#[requires="x <= 100"]
fn test1_fail(x: u8) {
    let perc = Percentage::new(x);
    assert!(perc.value <= 99); //~ ERROR assert!(..) statement might not hold
}

#[requires="x <= 100"]
fn test2(x: u8) {
    let mut perc = Percentage { value: x };
    perc.incr();
}

#[requires="x <= 101"] // mistake
fn test2_fail(x: u8) {
    let mut perc = Percentage { value: x }; // bogus construction
    perc.incr(); //~ ERROR precondition might not hold
}

#[requires="x <= 100"]
fn test3(x: u8) {
    let mut perc = Percentage { value: x };
    perc.incr();
    assert!(perc.value <= 100);
}

#[requires="x <= 100"]
fn test3_fail(x: u8) {
    let mut perc = Percentage { value: x };
    perc.incr();
    assert!(perc.value <= 99); //~ ERROR assert!(..) statement might not hold
}

fn main() {}
