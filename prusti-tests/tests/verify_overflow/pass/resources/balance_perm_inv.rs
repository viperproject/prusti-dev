#![allow(dead_code)]
use prusti_contracts::*;

#[resource]
struct Money();

#[invariant_twostate(PermAmount::from(self.balance()) >= holds(Money()))]
struct Bank { value: u32 }

impl Bank {

    #[pure]
    fn balance(&self) -> u32 {
        return self.value;
    }

    #[requires(transfers(Money(), amt))]
    #[requires(self.balance() >= amt)]
    fn withdraw(&mut self, amt: u32) {
        self.value -= amt;
    }
}

#[requires(transfers(Money(), 10))]
fn client(bank: &mut Bank) {
    bank.withdraw(10);
}

fn main() {

}
