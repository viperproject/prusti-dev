// compile-flags: -Punsafe_core_proof=true -Ponly_memory_safety=true

use prusti_contracts::*;

fn test() {
    let s0: Seq<u32> = Seq::empty();
}

fn main() {}
