// compile-flags: -Punsafe_core_proof=true -Penable_type_invariants=true -Pverify_specifications_with_core_proof=true
//
// These tests need core-proof for specs.

use prusti_contracts::*;

struct T1 {
    f: i32,
}

fn test01(mut a: T1, mut b: T1) {
    let z = b.f;
    let x = std::ptr::addr_of_mut!(a);
    let y = std::ptr::addr_of_mut!(b);
    unpack!(*x);
    unpack!((*x).f);
    unsafe { (*x).f = 4; }
    pack!(*x);
    restore!(*x, a);
    restore!(*y, b);
    assert!(a.f == 4);
    assert!(z == b.f);
}

fn test02(mut a: T1, mut b: T1) {
    let z = b.f;
    let x = std::ptr::addr_of_mut!(a);
    let y = std::ptr::addr_of_mut!(b);
    unpack!(*x);
    unpack!((*x).f);
    unsafe { (*x).f = 4; }
    pack!(*x);
    restore!(*x, a);
    restore!(*y, b);
    assert!(a.f == 5);  //~ ERROR: the asserted expression might not hold
}

fn main() {}
