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

fn test4() {
    let mut a = MyUnion { f1: 1 };
    assert!(unsafe { a.f1 == 1});
    a.f1 = 2;
    assert!(unsafe { a.f1 == 2});
}

fn test5() {
    let mut a = MyUnion { f1: 1 };
    assert!(unsafe { a.f1 == 1});
    a.f1 = 2;
    assert!(unsafe { a.f1 == 2});
    assert!(unsafe { a.f1 == 3}); //~ ERROR: the asserted expression might not hold
}

fn main() {}
