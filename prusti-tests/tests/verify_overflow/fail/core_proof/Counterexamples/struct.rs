// compile-flags: -Punsafe_core_proof=true -Pcounterexample=true

use prusti_contracts::*;


//#[derive(Copy, Clone)]
struct X{
    a: i32, 
    b: i32,
}


#[ensures(result)]
fn test(x: X) -> bool{
    x.a == x.b
}


fn main() {}