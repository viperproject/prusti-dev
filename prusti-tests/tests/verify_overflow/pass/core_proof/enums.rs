// compile-flags: -Punsafe_core_proof=true -Puse_smt_wrapper=true -Psmt_quantifier_instantiations_bound_global=10000 -Psmt_quantifier_instantiations_bound_trace=200 -Psmt_quantifier_instantiations_bound_trace_kind=5 -Psmt_quantifier_instantiations_bound_global_kind=20

use prusti_contracts::*;

struct T {
    f: u32,
}

enum E {
    V1(u32),
    V2(T),
    V3,
    V4 {
        g: u32,
    },
}

struct G {
    e: E,
}

fn branch1() {
    let a = T { f: 4 };
    let e = E::V2(a);
    let _x = match e {
        E::V1(g) => g,
        E::V2(T { f }) => f,
        E::V3 => 1,
        E::V4 { g } => g,
    };
}

fn test1() {
    let d = !false;
    let a = Some(5u32);
    let _x = match a {
        Some(y) => y,
        None => 4,
    };
}

fn test2() {
    let a = T { f: 4 };
    let _b = E::V2(a);
}

fn test3() {
    let a = T { f: 4 };
    let b = E::V2(a);
    let _c = G { e: b };
}

fn main() {}

