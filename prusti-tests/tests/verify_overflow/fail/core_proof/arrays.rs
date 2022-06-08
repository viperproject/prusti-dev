// compile-flags: -Punsafe_core_proof=true

use prusti_contracts::*;

fn test1() {
    let a = [1, 2];
}

fn test2() {
    let a = [1, 2];
    assert!(false);     //~ ERROR: the asserted expression might not hold
}

fn test3() {
    let a = [1; 100];
}

fn test4() {
    let a = [1; 100];
    let b = a[1];
    assert!(b == 1);
}

fn test5() {
    let a = [1; 100];
    let b = a[1];
    assert!(b == 6);     //~ ERROR: the asserted expression might not hold
}

fn test6() {
    let a = [1; 100];
    let b = a[1];
    let c = a[2];
    assert!(b == 1);
    assert!(c == 1);
}

fn test7() {
    let a = [1; 100];
    let b = a[1];
    let c = a[2];
    assert!(b == 1);
    assert!(c == 2);     //~ ERROR: the asserted expression might not hold
}

fn main() {}
