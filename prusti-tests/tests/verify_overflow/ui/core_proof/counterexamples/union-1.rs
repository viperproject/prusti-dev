// compile-flags: -Punsafe_core_proof=true -Pcounterexample=true

use prusti_contracts::*;

union MyUnion {
    f1: u32,
    f2: i32,
}

#[ensures(false)]
fn test1() {
    let a = MyUnion { f1: 1 };
    let _x = unsafe { a.f1 };
}

fn test2() {
    let mut a = MyUnion { f1: 1 };
    assert!(unsafe { a.f1 == 1});
    a.f1 = 2;
    assert!(unsafe { a.f1 == 2});
    assert!(unsafe { a.f1 == 3});
}

fn main() {}
