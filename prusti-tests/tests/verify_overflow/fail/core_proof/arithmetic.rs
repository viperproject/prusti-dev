// compile-flags: -Punsafe_core_proof=true -Psmt_quant_instantiations_bound=1000

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

fn main() {}
