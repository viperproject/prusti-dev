// ignore-test
#![allow(dead_code)]
use prusti_contracts::*;

#[resource_kind]
struct Money();

#[invariant_twostate(
        holds(Money()) - old(holds(Money())) ==
        PermAmount::from(self.balance()) - PermAmount::from(old(self.balance()))
    )
]
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


    #[trusted]
    #[after_expiry(before_expiry(self.balance()) == old(self.balance()))]
    fn get_mut_value(&mut self) -> &mut u32 {
        &mut self.value
    }
}

fn hack_balance(bank: &mut Bank){
    bank.get_mut_value();
}

#[requires(resource(Money(), 10))]
fn client(bank: &mut Bank) {
    bank.withdraw(10);
}

fn main() {

}
