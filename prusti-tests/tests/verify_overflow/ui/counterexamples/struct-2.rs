// compile-flags: -Punsafe_core_proof=true -Pcounterexample=true

use prusti_contracts::*;

#[derive(Copy, Clone)]
struct X{
    a: i32, 
    b: i32,
}

#[pure]
#[requires(x.a == 5)] // force specific counterexample
#[ensures(!result)]
fn test_pure(x: X) -> bool{
    x.a == x.b
}

#[requires(x.a == 0 && a == -2 && x.b == 3)] // force specific counterexample
#[ensures(result)]
fn test_mut(x: &mut X, a: i32) -> bool{
    x.a = a;
    x.b = 1;
    x.a = 2;
    x.a = a;
    x.a > 0
}

fn main() {}
