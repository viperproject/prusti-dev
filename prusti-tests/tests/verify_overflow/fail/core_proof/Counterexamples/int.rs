// compile-flags: -Punsafe_core_proof=true -Pcounterexample=true

use prusti_contracts::*;

fn test1(a: i32, b: i32) {
    let c = a + b;
    assert!(c == 3);
}

#[requires(a == b)]
fn test2(a: u32, b: u32) {
    let c = a - b;
    assert!(c != 0);  
}


fn main() {}