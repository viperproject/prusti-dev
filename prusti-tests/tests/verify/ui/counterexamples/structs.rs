// compile-flags: -Pcounterexample=true

use prusti_contracts::*;

struct Account {
    balance: i32,
}

#[requires(amount == 3 && x.balance == 5 && y.balance == 1)] // force specific counterexample
#[requires(amount > 0)]
#[requires(x.balance > amount)]
#[requires(y.balance >= 0)]
#[ensures(old(y.balance) > result.1.balance)]
fn test1(
    mut x: Account,
    mut y: Account,
    amount: i32,
) -> (Account, Account) {
    if x.balance >= amount {
        let temp = y.balance;
        x.balance -= amount;
        y.balance += amount;
    }
    (x, y)
}

struct A {
    value: i32,
    other_value: i32,
    valid: bool,
}

#[requires(x.value == 1 && x.other_value == 2)] // force specific counterexample
fn test2(x: A) {
    assert!(x.value == x.other_value || x.valid);
}

struct B {
    x: i32,
    y: i32,
}

fn test3(x: B) {
    if x.x == 5 && x.y == 10 {
        assert!(x.x == x.y)
    }
}

fn main() {}
