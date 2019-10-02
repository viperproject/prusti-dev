#![allow(dead_code, non_snake_case)]
extern crate prusti_contracts;

struct Account {
    bal: u32,
}

impl Account {

    #[pure]
    fn balance(&self) -> u32 {
        self.bal
    }

    #[ensures="self.balance() == old(self.balance()) + amount"]
    fn deposit(&mut self, amount: u32) {
        self.bal = self.bal + amount;
    }

    #[requires="amount <= self.balance()"]
    #[ensures="self.balance() == old(self.balance()) - amount"]
    fn withdraw(&mut self, amount: u32) {
        self.bal = self.bal - amount;
    }

    #[ensures="self.balance() == old(self.balance()) - amount"]
    fn transfer(&mut self, other: &mut Account, amount: u32) {
        self.withdraw(amount); //~ ERROR precondition might not hold
        other.deposit(amount);
    }
}

fn main() {}
