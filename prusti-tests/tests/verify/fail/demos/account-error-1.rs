#![allow(dead_code, non_snake_case)]
use prusti_contracts::*;

struct Account {
    bal: u32,
}

impl Account {

    #[pure]
    fn balance(&self) -> u32 {
        self.bal
    }

    #[ensures(self.balance() == old(self.balance()) + amount)]
    fn deposit(&mut self, amount: u32) {
        self.bal = self.bal + amount;
    }

    #[requires(amount <= self.balance())]
    #[ensures(self.balance() == old(self.balance()) - amount)]
    fn withdraw(&mut self, amount: u32) {
        self.bal = self.bal - amount;
    }

    #[requires(amount <= self.balance())]
    #[ensures(self.balance() == old(self.balance()) + amount)] //~ ERROR postcondition might not hold
    fn transfer(&mut self, other: &mut Account, amount: u32) {
        self.withdraw(amount);
        other.deposit(amount);
    }
}

fn main() {}
