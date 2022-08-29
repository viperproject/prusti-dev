// compile-flags: -Punsafe_core_proof=true -Pcounterexample=true

use prusti_contracts::*;

//a counterexample can only be generated for directly accessed elements of a sequence

fn test1() {
    let mut a = [1; 2];
    a[0] = 2;
    assert!(a[1] == 2);
}

#[ensures(result)]
fn test2() -> bool {
    let a = [1, 2, 3, 4];
    a[0] == a[1]   
}

fn main() {}
