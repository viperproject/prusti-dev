// compile-flags: -Punsafe_core_proof=true -Puse_smt_wrapper=true -Psmt_quantifier_instantiations_bound_global=10000 -Psmt_quantifier_instantiations_bound_trace=200 -Psmt_quantifier_instantiations_bound_trace_kind=20 -Psmt_quantifier_instantiations_bound_global_kind=60
//
// Note: it should be impossible to prove that two pointers are **not**
// equal because compiler optimizations may make them equal. This is
// currently achieved by not modelling any disequalities between Address
// types (unlike for Viper's builtin Refs, for Address having more than
// full permission does not imply that addresses are different).

use prusti_contracts::*;

fn test1() {
    let a = 4u32;
    let _x = std::ptr::addr_of!(a);
}

fn test2() {
    let mut a = 4u32;
    let _x = std::ptr::addr_of_mut!(a);
}

fn test3() {
    let a = 4u32;
    let x = std::ptr::addr_of!(a);
    let y = std::ptr::addr_of!(a);
    assert!(x == y);
}

fn test4() {
    let a = 4u32;
    let b = 4u32;
    let x = std::ptr::addr_of!(a);
    let y = std::ptr::addr_of!(b);
    assert!(x == y);    //~ ERROR
}

fn test5() {
    let a = 4u32;
    let b = 4u32;
    let x = std::ptr::addr_of!(a);
    let y = std::ptr::addr_of!(b);
    assert!(x != y);    //~ ERROR
}

fn test6() {
    let a = 4u32;
    let b = 4u32;
    let x = std::ptr::addr_of!(a);
    let y = std::ptr::addr_of!(b);
    assert!(!(x == y));    //~ ERROR
}

struct T {
    g: u32,
}

struct G {
    f: T,
}

fn test7() {
    let a = 4u32;
    let b = T { g: a };
    let c = G { f: b };
    let x = std::ptr::addr_of!(a);
    let y = std::ptr::addr_of!(c.f.g);
    assert!(x != y);    //~ ERROR
}

fn test8() {
    let a = 4u32;
    let b = T { g: a };
    let c = G { f: b };
    let x = std::ptr::addr_of!(a);
    let y = std::ptr::addr_of!(c.f.g);
    assert!(!(x == y));    //~ ERROR
}

fn test9() {
    let a = 4u32;
    let b = T { g: a };
    let c = G { f: b };
    let x = std::ptr::addr_of!(a);
    let y = std::ptr::addr_of!(c.f.g);
    assert!(x == y);    //~ ERROR
}

fn main() {}
