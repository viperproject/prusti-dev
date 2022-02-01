extern crate prusti_contracts;
use prusti_contracts::*;

/// External traits
trait ExternTrait {
    fn foo(&self) -> i32;
    fn bar(&self) -> i32;
}
/// External traits

#[extern_spec]
trait ExternTrait {
    #[ensures(result == 42)]
    fn foo(&self) -> i32;
}

struct S;

impl ExternTrait for S {
    fn foo(&self) -> i32 {
        42
    }

    fn bar(&self) -> i32 {
        43
    }
}

fn main() {
    let s = S {};
    assert!(s.foo() == 42);
}