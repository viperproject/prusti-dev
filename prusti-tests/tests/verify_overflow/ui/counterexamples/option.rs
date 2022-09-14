// compile-flags: -Punsafe_core_proof=true -Pcounterexample=true

use prusti_contracts::*;

struct X{
    a: Option<i32>,
}

#[ensures(!result)]
fn test_1(x: X) -> bool {
    match x.a {
        Some(2) => true,
        _ => false,
    }
}


fn main(){}