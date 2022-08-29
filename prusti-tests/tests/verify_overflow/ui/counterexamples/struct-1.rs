// compile-flags: -Punsafe_core_proof=true -Pcounterexample=true -Pcheck_overflows=false

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
/*
struct A {
    value: i32,
    other_value: i32,
    valid: bool,
}


FIXME: unhandled verification error: Exhale might fail. There might be insufficient 
permission to access MemoryBlock(_8$address, Size$Bool$(constructor$Snap$Usize$(1))) (@35.47)

fn test2(x: A) {
    assert!(x.value == x.other_value || x.valid);
}


struct B {
    x: i32,
    y: i32,
}

FIXME: Details: unexpected verification error: [exhale.failed:insufficient.permission] 
Exhale might fail. There might be insufficient permission to access 
MemoryBlock(_5$address, Size$Bool$(constructor$Snap$Usize$(1))) (@44.28)

fn test3(x: B) {
    if x.x == 5 && x.y == 10 {
        assert!(x.x == x.y)
    }
}*/

fn main() {}
