use prusti_contracts::*;

trait Trait {
    #[pure]
    fn foo(&self) -> i32 { 1 }
}

struct Struct;
impl Trait for Struct {
    // inherits the annotation from the trait
    fn foo(&self) -> i32 {
        42
    }
}

fn main() {
    let s = Struct {};
    assert!(s.foo() == 42);
}