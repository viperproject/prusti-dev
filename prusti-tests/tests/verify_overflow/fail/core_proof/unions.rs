// compile-flags: -Punsafe_core_proof=true -Ponly_memory_safety=true

use prusti_contracts::*;

union MyUnion {
    f1: u32,
    f2: i32,
}

fn test1() {
    let u = MyUnion { f1: 1 };
}

fn main() {}
