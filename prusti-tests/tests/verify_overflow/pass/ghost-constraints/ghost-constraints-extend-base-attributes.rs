// compile-flags: -Penable_ghost_constraints=true
// This test demonstrates that ghost constraints inherit the specs from the function.

use prusti_contracts::*;

trait A {}
impl A for i32 {}

#[pure]
#[trusted]
#[ghost_constraint(T: A, [
    ensures(result == 42)
])]
fn constrained_contract_stays_pure<T>(_x: &T) -> i32 {
    42
}

#[requires(constrained_contract_stays_pure::<i32>(&a) == 42)]
fn verify_constrained_contract_stays_pure(a: i32) {}

#[trusted]
#[ensures(result % 2 == 0)]
#[ghost_constraint(T: A, [
    ensures(result == 42)
])]
fn constrained_contract_inherits_posts<T>(_x: T) -> i32 {
    42
}

fn verify_constrained_contract_inherits_posts() {
    let res = constrained_contract_inherits_posts(32 as u32);
    assert!(res % 2 == 0);
    // assert!(res == 42); // <- can not prove this

    let res = constrained_contract_inherits_posts(32 as i32);
    assert!(res == 42);
}

fn main() {
}