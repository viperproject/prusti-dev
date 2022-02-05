// compile-flags: -Punsafe_core_proof=true

use prusti_contracts::*;

struct T {
    val: i32
}

struct T2 {
    f1: T,
    f2: T,
}

fn construct() {
    let a = T { val: 4 };
    let _b = T2 { f1: T { val: 5 }, f2: a };
}

fn main() {}
