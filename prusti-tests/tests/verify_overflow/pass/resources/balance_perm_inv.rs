#![allow(dead_code)]
use prusti_contracts::*;

#[resource_kind]
struct Money();

#[invariant_twostate(
        holds(Money()) - old(holds(Money())) ==
        PermAmount::from(self.balance()) - PermAmount::from(old(self.balance()))
    )
]
#[invariant(PermAmount::from(self.balance()) >= holds(Money()))]
struct Bank { value: u32 }

impl Bank {

    #[pure]
    fn balance(&self) -> u32 {
        return self.value;
    }

    #[requires(resource(Money(), amt))]
    fn withdraw(&mut self, amt: u32) {
        self.value -= amt;
    }
}

#[requires(resource(Money(), 10))]
fn client(bank: &mut Bank) {
    bank.withdraw(10);
}

fn main() {

}
