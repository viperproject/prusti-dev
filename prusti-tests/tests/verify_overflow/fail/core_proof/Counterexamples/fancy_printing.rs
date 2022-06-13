// compile-flags: -Punsafe_core_proof=true -Pcounterexample=true

use prusti_contracts::*;

#[print_counterexample("text {} {}", a, b)]
struct X{
    a: i32, 
    b: i32,
}

/*
#[ensures(result)]
fn test(x: X) -> bool{
    x.a == x.b
}*/

#[ensures(!result)]
fn test_mut(x: X, a: i32) -> bool{
    prusti_assume!(a > 0);
    x.a == a
}

fn main() {}