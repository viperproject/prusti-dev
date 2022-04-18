// compile-flags: -Punsafe_core_proof=true

use prusti_contracts::*;

struct T {
    f: u32,
}

struct T2 {
    f: u32,
}

impl Drop for T {
    fn drop(&mut self) {}
}

fn test1() {
    {
        let a = T { f: 4 };
    }
    let b = T2 { f: 4 };
}

fn test2() {
    let b = T2 { f: 4 };
    assert!(b.f == 5);  //~ ERROR the asserted expression might not hold
}

fn main() {}

