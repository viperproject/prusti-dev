// compile-flags: -Punsafe_core_proof=true -Pcounterexample=true

use prusti_contracts::*;


struct X {
    a: A,
    b: B,
}

#[model]
struct X {
   a: i32,
   b: i32,
}

#[derive(Copy, Clone)]
struct A {
    a: i32,
}

#[derive(Copy, Clone)]
struct B {
    b: i32,
}

#[ensures(x.model().a == x.model().b)]
fn test1(x: X) {}

#[ensures(x.model().b == y.model().a)]
fn test2(x: X, y: X) {}

fn main() {}