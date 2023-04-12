#![allow(dead_code, unused)]
use prusti_contracts::*;

type BankID = u32;

#[resource_kind]
struct Money(BankID);

struct Bank();


impl Bank {

    #[pure]
    fn id(&self) -> BankID {
        42
    }

    #[ensures(holds(Money(self.id())) == PermAmount::from(0))]
    fn transfer_tokens(
        &mut self,
    ) { }

    #[ensures(holds(Money(self.id())) == PermAmount::from(0))]
    fn transfer_tokens_client(
        &mut self,
    ) {
        self.transfer_tokens();
    }

}




pub fn main(){}
