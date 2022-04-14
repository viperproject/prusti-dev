// compile-flags: -Punsafe_core_proof=true

use prusti_contracts::*;

fn test1() {
    let mut a = 1;
    let _b = &mut a;
}

fn main() {}
