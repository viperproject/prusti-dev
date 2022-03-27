// compile-flags: -Punsafe_core_proof=true -Ponly_memory_safety=true

use prusti_contracts::*;

union MyUnion {
    f1: u32,
    f2: i32,
}

fn test1() {
    let a = MyUnion { f1: 1 };
    let _x = unsafe { a.f1 };
}

fn test2() {
    let a = MyUnion { f1: 1 };
    let _x = unsafe { a.f1 };
    let _y = unsafe { a.f2 };   //~ ERROR: failed to obtain the required capability because a conflicting capability is present
}

fn test3() {
    let a = MyUnion { f1: 1 };
    let _y = unsafe { a.f2 };   //~ ERROR: failed to unpack the capability of union's field
}

fn main() {}
