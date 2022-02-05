// compile-flags: -Punsafe_core_proof=true -Ponly_memory_safety=true

use prusti_contracts::*;

fn branch1() {
    let mut a = 1;
    if true {
        a = 3;
    }
    let _b = a;
}

struct T {
    f: u32,
}

fn branch2(b: bool) {
    let mut a = T { f: 4 };
    if b {
        let _c = a;
    }
}

fn main() {}

