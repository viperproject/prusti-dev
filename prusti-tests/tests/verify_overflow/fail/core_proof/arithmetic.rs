// compile-flags: -Punsafe_core_proof=true

use prusti_contracts::*;

fn test1() {
    let a = 1;
    let b = 2;
    let c = a + b;
    assert!(c == 3);
}

fn test2() {
    let a = 1;
    let b = 2;
    let c = a + b;
    assert!(c == 4);    //~ ERROR the asserted expression might not hold
}

fn test3(a: i32, b: i32) -> i32 {
    a + b   //~ ERROR assertion might fail with "attempt to add with overflow"
}

fn test4() {
    let x = 1 / 3;
    assert!(x == 0);
    let x = 4 / 3;
    assert!(x == 1);
}

fn test5() {
    let x = 1 / 3;
    assert!(x == 1);    //~ ERROR: the asserted expression might not hold
}

fn test6() {
    let x = 1 * 3;
    assert!(x == 3);
}

fn test7() {
    let x = 1 * 3;
    assert!(x == 1);    //~ ERROR: the asserted expression might not hold
}

fn main() {}
