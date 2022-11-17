// compile-flags: -Punsafe_core_proof=true -Pcounterexample=true

use prusti_contracts::*;

#[ensures(!result)]
fn test1(x: char) -> bool {
    x == 'c'
}

fn main() {}
