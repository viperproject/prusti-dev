#![allow(dead_code)]
#![allow(unused_variables)]
use prusti_contracts::*;

#[invariant(self.value <= 100)]
struct Percentage {
    value: u8,
}

impl Percentage {
    //#[ensures(assert_on_expiry(*result <= 100))]
    fn leak(&mut self) -> &mut u8 { //~ ERROR pledge in the postcondition might not hold
        &mut self.value
    }
}

//#[requires(value <= 100)]
fn test(p: &mut Percentage, value: u8) {
    assert!(p.value <= 100);
    let r = p.leak();
    *r = value;
    assert!(p.value <= 100);
}

fn main() {}
