// compile-flags: -Penable_ghost_constraints=true

use prusti_contracts::*;

trait A {
    type AType;

    #[pure]
    fn foo(&self, arg1: &Self::AType) -> bool;
}

trait B {
    type BType;

    #[ghost_constraint(Self: A<AType = <Self as B>::BType> , [
    requires(self.foo(&arg)),
    ensures(self.foo(&arg))
    ])]
    #[trusted]
    fn bar(&self, arg: Self::BType);
}

struct S;
impl A for S {
    type AType = i32;
    #[pure]
    fn foo(&self, arg1: &Self::AType) -> bool {
        *arg1 > 42
    }
}

impl B for S {
    type BType = i32;

    #[trusted]
    fn bar(&self, arg: Self::BType) {

    }
}

fn main() {
    let s = S;
    s.bar(43);
}