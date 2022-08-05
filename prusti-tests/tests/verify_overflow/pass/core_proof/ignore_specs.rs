// compile-flags: -Punsafe_core_proof=true -Pverify_specifications=false

use prusti_contracts::*;

fn test1() {
    assert!(false);
}

fn test2() {
    prusti_assert!(false);
}

#[requires(false)]
fn test3() { }

fn test4() {
    test3();
}

fn main() {}
