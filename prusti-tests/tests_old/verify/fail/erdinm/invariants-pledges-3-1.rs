#![allow(dead_code)]
#![allow(unused_variables)]
use prusti_contracts::*;

#[invariant(self.value <= 100)]
struct Percentage {
    value: u8,
}

impl Percentage {
    //#[ensures(*result <= 100)]
    #[ensures(assert_on_expiry(*result <= 100))]
    fn leak(&mut self) -> &mut u8 {
        &mut self.value
    }
}

fn test(p: &mut Percentage, value: u8) {
    assert!(p.value <= 100);
    let r = p.leak(); //~ ERROR obligation might not hold on borrow expiry
    assert!(p.value <= 100);
}

fn main() {}
