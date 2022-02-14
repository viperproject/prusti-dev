extern crate prusti_contracts;
use prusti_contracts::*;

trait Trait {
    fn foo(&self) -> i32;
}

struct Struct1;
struct Struct2;

impl Trait for Struct1 {
    fn foo(&self) -> i32 {
        42
    }
}

impl Trait for Struct2 {
    fn foo(&self) -> i32 {
        43
    }
}

#[extern_spec]
impl Trait for Struct1 {
    #[ensures( result == 42 )]
    fn foo(&self) -> i32;
}

fn main() {
    let s1 = Struct1 {};
    assert!(s1.foo() == 42);

    let s2 = Struct2 {};
    assert!(s2.foo() == 43); //~ ERROR: the asserted expression might not hold
}