#![allow(dead_code, unused)]
use prusti_contracts::*;

#[derive(Copy, Clone)]
struct AccountID(u32);

#[resource_kind]
struct Money(AccountID);

struct Bank(u32);


impl Bank {

    #[pure]
    #[trusted]
    fn balance(&self, account_id: AccountID) -> u32 {
        unimplemented!()
    }

    #[requires(resource(Money(acct_id), amt))]
    #[ensures(
            old(holds(Money(acct_id))) ==
            PermAmount::from(old(self.balance(acct_id))) - PermAmount::from(self.balance(acct_id))
    )]
    #[trusted]
    fn withdraw(&mut self, acct_id: AccountID, amt: u32) { 
        unimplemented!()
    }
}


#[requires(resource(Money(from), 10))]
#[ensures(
    old(holds(Money(from))) ==
    PermAmount::from(old(bank.balance(from))) - PermAmount::from(bank.balance(from))
)]
fn client(bank: &mut Bank, from: AccountID) {
    bank.withdraw(from, 10);
}

pub fn main(){}
