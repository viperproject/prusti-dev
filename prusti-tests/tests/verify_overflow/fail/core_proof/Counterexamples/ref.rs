// compile-flags: -Punsafe_core_proof=true -Pcounterexample=true

use prusti_contracts::*;


//#[derive(Copy, Clone)]
struct X{
    a: i32, 
    b: i32,
}

/*
#[ensures(result)]
fn test(x: &mut X) -> bool{
    x.a == x.b
}*/

fn test2() {
    let mut a = 1;
    let _b = &mut a;
    *_b = 2;
    *_b = 10;
    assert!(a == 1);    //~ ERROR: the asserted expression might not hold
}


fn main() {}