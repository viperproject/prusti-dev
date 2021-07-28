// compile-flags: -Pcounterexample=true

// ignore-test
// TODO: the counterexample for `has_money` should show an account with a
// non-positive balance, but it only shows "?". The issue is the indirection
// through a function call.

use prusti_contracts::*;

pub struct Account {
    balance: i32,
}

#[pure]
fn get_balance(acc: Account) -> i32 {
    acc.balance
}

#[ensures(result)]
fn has_money(acc: Account) -> bool {
    get_balance(acc) > 0
}

fn main() {}
