// compile-flags: -Punsafe_core_proof=true -Puse_smt_wrapper=true -Psmt_qi_bound_global=10000 -Psmt_qi_bound_trace=200 -Psmt_qi_bound_trace_kind=5 -Psmt_qi_bound_global_kind=20

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

