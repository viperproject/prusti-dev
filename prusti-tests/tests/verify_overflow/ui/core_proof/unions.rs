// compile-flags: -Punsafe_core_proof=true

use prusti_contracts::*;

union MyUnion {
    f1: u32,
    f2: i32,
}

fn test1() {
    let a = MyUnion { f1: 1 };
    let _x = unsafe { a.f1 };
    let _y = unsafe { a.f2 };
}

fn main() {}

