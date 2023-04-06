#![allow(dead_code, unused)]
use std::convert::TryInto;
use prusti_contracts::*;


#[invariant_twostate(
        holds(Money(self.id())) -
        old(holds(Money(self.id()))) ==
        PermAmount::from(self.balance()) -
            PermAmount::from(old(self.balance()))
    )
]
struct Bank(u32);

type BankID = u32;

#[resource]
struct Money(BankID);

type AccountID = u32;

impl Bank {

    #[pure]
    #[trusted]
    fn id(&self) -> BankID {
        unimplemented!()
    }

    #[pure]
    #[trusted]
    fn balance(&self) -> u32 {
        unimplemented!()
    }

    fn transfer_tokens(&mut self) {
        self.burn_tokens();
    }

    #[trusted]
    fn burn_tokens(&mut self) {
        unimplemented!()
    }
}

pub fn main(){}
