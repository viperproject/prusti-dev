// compile-flags: -Punsafe_core_proof=true -Psmt_quant_instantiations_bound=1000

use prusti_contracts::*;

struct T {
    val: i32
}

struct T2 {
    f1: T,
    f2: T,
}

fn construct() {
    let c = true;
    let a = T { val: 4 };
    let _b = T2 { f1: T { val: 5 }, f2: a };
}

fn construct2() {
    let a = T { val: 4 };
    let _b = (T { val: 5}, a);
}

fn copy() {
    let a = true;
    let b = !a;
}

fn main() {}
