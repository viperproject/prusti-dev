// compile-flags: -Penable_ghost_constraints=true

use prusti_contracts::*;

trait A {}

trait MyTrait {
    #[ensures(result > 0)]
    #[ghost_constraint(Self: A, [
    ensures(result % 2 == 0)
    ])]
    fn foo(&self) -> i32;
}

struct MyStruct;
#[refine_trait_spec]
impl MyTrait for MyStruct {

    #[ensures(result > 10)]
    #[ghost_constraint(Self: A, [ //~ ERROR: Ghost constraints in trait spec refinements not supported
    ensures(result % 6 == 0)
    ])]
    fn foo(&self) -> i32 {
        42
    }
}

fn main() {
    // MyStruct does not implement A
    let s = MyStruct;
    assert!(s.foo() > 0);
}
