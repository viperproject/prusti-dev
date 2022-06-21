// compile-flags: -Pcheck_no_drops=true -Punsafe_core_proof=true -Puse_smt_wrapper=true -Psmt_quantifier_instantiations_bound_global=10000 -Psmt_quantifier_instantiations_bound_trace=200 -Psmt_quantifier_instantiations_bound_trace_kind=15 -Psmt_quantifier_instantiations_bound_global_kind=20

use prusti_contracts::*;

struct T {
    f: u32,
}

struct T2 {
    f: u32,
}

struct T3 {
    g: T,
}

impl Drop for T {
    fn drop(&mut self) {}
}

fn test1() {
    {
        let a = T { f: 4 };
    }   //~ ERROR the drop handler was called.
    let b = T2 { f: 4 };
}

fn test2() {
    {
        let a = T2 { f: 4 };
    }
    let b = T2 { f: 4 };
}

fn test3() {
    {
        let a = T2 { f: 4 };
        drop(a);
    }
    let b = T2 { f: 4 };
}

fn test4() {
    let a = T { f: 4 };
    let b = T3 { g: a };
}   //~ ERROR the drop handler was called.

fn test5() {
    let a = T { f: 4 };
    let b = T3 { g: a };
    drop(b);
}

fn test6() {
    let a = T { f: 4 };
    let b = T3 { g: a };
    drop(b.g);
}

fn random() -> bool {
    false
}

fn test7() {
    let a = T { f: 4 };
    let b = T3 { g: a };
    if random() {
        drop(b.g);
    }
}    //~ ERROR the drop handler was called.

fn test8() {
    let c = random();
    let a = T { f: 4 };
    let b = T3 { g: a };
    if c {
        drop(b.g);
    } else {
        drop(b);
    }
}

// Compared to test8, the drop handler is called in a case when `random`
// panics.
fn test9() {
    let a = T { f: 4 };
    let b = T3 { g: a };
    if random() {
        drop(b.g);
    } else {
        drop(b);
    }
}    //~ ERROR the drop handler was called.

fn main() {}

