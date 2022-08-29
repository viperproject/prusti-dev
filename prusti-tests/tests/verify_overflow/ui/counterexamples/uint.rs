// compile-flags: -Punsafe_core_proof=true -Pcounterexample=true -Pcheck_overflows=false

use prusti_contracts::*;

#[ensures(result != 42)]
fn foo(x: u32) -> u32 {
    let y = x + 1;
    y * 2
}

fn main() {}
