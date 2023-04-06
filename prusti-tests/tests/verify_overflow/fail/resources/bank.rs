#![allow(dead_code)]
use prusti_contracts::*;

#[derive(Copy, Clone)]
struct AccountId(u32);

#[resource]
struct Money(AccountId);

trait Bank {

    fn balance(&self, acct_id: AccountId) -> u32;

    #[ensures(transfers(Money(acct_id), amt))]
    fn deposit(&mut self, acct_id: AccountId, amt: u32);

    #[requires(transfers(Money(acct_id), amt))]
    fn withdraw(&mut self, acct_id: AccountId, amt: u32);
}

#[ensures(transfers(Money(acct_id), 4))]
fn good_client<B: Bank>(bank: &mut B, acct_id: AccountId) {
    bank.deposit(acct_id, 10);
    bank.withdraw(acct_id, 6);
}

fn bad_client<B: Bank>(bank: &mut B, acct_id: AccountId) {
    bank.deposit(acct_id, 10);
    bank.withdraw(acct_id, 5);
    bank.withdraw(acct_id, 6); //~ ERROR insufficient permission
}

fn bad_client_2<B: Bank>(bank: &mut B) {
    let acct_id = AccountId(1);
    good_client(bank, acct_id);
    bank.withdraw(acct_id, 5); //~ ERROR insufficient permission
}

fn main() {

}
