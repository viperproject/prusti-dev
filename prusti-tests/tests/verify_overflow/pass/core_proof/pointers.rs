// compile-flags: -Punsafe_core_proof=true -Psmt_quant_instantiations_bound=1000

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
