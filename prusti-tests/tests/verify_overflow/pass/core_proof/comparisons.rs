// compile-flags: -Punsafe_core_proof=true -Ponly_memory_safety=true

use prusti_contracts::*;

fn test1() {
    let a = 4u32;
    let b = 4u32;
    let c = 5u32;
    assert!(a == b);
    assert!(a != c);
    assert!(!(a == c));
    assert!(a < c);
    assert!(a <= c);
}

fn main() {}
