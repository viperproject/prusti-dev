// compile-flags: -Punsafe_core_proof=true -Pcounterexample=true -Pprint_counterexample_if_model_is_present=true

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

#[requires(x.model().a == 5)] //force specific counterexample
#[requires(x.model().a == x.a.a)]
#[requires(x.model().b == x.b.b)]
#[ensures(!(x.model().a == x.model().b))]
fn test1(x: X) {}

#[requires(x.model().b == 5 && x.model().a == 2 && y.model().b == 2)] //force specific counterexample
#[requires(x.model().a == x.a.a)]
#[requires(x.model().b == x.b.b)]
#[requires(y.model().a == y.a.a)]
#[requires(y.model().b == y.b.b)]
#[ensures(x.model().b == y.model().a)]
fn test2(x: X, y: X) {}

fn main() {}