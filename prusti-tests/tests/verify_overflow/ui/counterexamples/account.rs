// compile-flags: -Punsafe_core_proof=true -Pcounterexample=true

use prusti_contracts::*;

#[derive(Copy, Clone)]
pub struct Account {
    balance: i32,
}

#[pure]
fn get_balance(acc: Account) -> i32 {
    acc.balance
}

#[requires(acc.balance >= 0)] //force specific counterexample
#[ensures(result)]
fn has_money(acc: Account) -> bool {
    get_balance(acc) > 0
}

fn main() {}
