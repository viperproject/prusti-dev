// compile-flags: -Punsafe_core_proof=true -Pcounterexample=true

use prusti_contracts::*;


//#[derive(Copy, Clone)]
struct X{
    a: i32, 
    b: i32,
}

/*
#[ensures(result)]
fn test(x: X) -> bool{
    x.a == x.b
}*/

#[requires(x.a > 0)]
#[ensures(result)]
fn test_mut(mut x: X, a: i32) -> bool{
    x.a = 1;
    x.b = 1;
    x.a = 2;
    x. a = a;
    x.a > 0
}

fn main() {}