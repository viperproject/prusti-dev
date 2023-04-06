#![allow(dead_code)]
use prusti_contracts::*;

#[derive(Copy, Clone)]
struct AccountId(u32);

#[resource]
struct Money(AccountId);

trait Bank {

    #[pure]
    fn withdraw_pre(&self, acct_id: AccountId, amt: u32) -> bool {
        transfers(Money(acct_id), amt) //~ ERROR use of impure function
    }

    #[requires(self.withdraw_pre(acct_id, amt))]
    fn withdraw(&mut self, acct_id: AccountId, amt: u32);
}

fn main() {

}
