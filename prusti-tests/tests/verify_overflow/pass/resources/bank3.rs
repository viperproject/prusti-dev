#![allow(dead_code, unused)]
use prusti_contracts::*;

type BankID = u32;

#[resource]
struct Money();

struct Bank(u32);


impl Bank {

    #[pure]
    #[trusted]
    fn balance(&self) -> u32 {
        unimplemented!()
    }

    #[requires(transfers(Money(), amt))]
    #[ensures(
            holds(Money()) - old(holds(Money())) ==
            PermAmount::from(self.balance() - old(self.balance()))
    )]
    #[trusted]
    fn withdraw(&mut self, amt: u32) { 
        unimplemented!()
    }

    #[ensures(transfers(Money(), amt))]
    #[ensures(
            holds(Money()) - old(holds(Money())) ==
            PermAmount::from(self.balance() - old(self.balance()))
    )]
    #[trusted]
    fn deposit(&mut self, amt: u32) { 
        unimplemented!()
    }
}

#[requires(transfers(Money(), 10))]
#[ensures(
        holds(Money()) - old(holds(Money())) ==
        PermAmount::from(bank.balance() - old(bank.balance()))
)]
fn client(bank: &mut Bank) {
    bank.withdraw(10);
}

pub fn main(){}
