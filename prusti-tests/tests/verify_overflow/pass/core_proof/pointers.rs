// compile-flags: -Punsafe_core_proof=true -Puse_smt_wrapper=true -Psmt_quantifier_instantiations_bound_global=10000 -Psmt_quantifier_instantiations_bound_trace=200 -Psmt_quantifier_instantiations_bound_trace_kind=5 -Psmt_quantifier_instantiations_bound_global_kind=20

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

fn main() {}
