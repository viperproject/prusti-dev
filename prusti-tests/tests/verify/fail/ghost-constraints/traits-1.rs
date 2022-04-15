// compile-flags: -Penable_ghost_constraints=true

use prusti_contracts::*;

trait A {}

trait MyTrait {
    #[ghost_constraint(Self: A, [ensures(result > 0)])]
    #[trusted]
    fn foo(&self) -> i32;
}

struct MyStruct;

impl MyTrait for MyStruct {
    fn foo(&self) -> i32 {
        42
    }
}

fn main() {
    let s = MyStruct;
    assert!(s.foo() > 0); //~ ERROR: the asserted expression might not hold
}