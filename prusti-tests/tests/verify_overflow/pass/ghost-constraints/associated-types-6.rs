// compile-flags: -Penable_ghost_constraints=true

use prusti_contracts::*;

trait A<'a> {
    type AType;
}

trait B<'a> {
    type BType;

    #[ghost_constraint(Self: A<'a, AType = <Self as B<'a>>::BType> , [
        ensures(*result > 0)
    ])]
    #[trusted]
    fn foo(&'a self) -> &'a i32;
}

struct S {
    val: i32,
}
impl<'a> A<'a> for S {
    type AType = &'a i32;
}

impl<'a> B<'a> for S {
    type BType = &'a i32;

    #[trusted]
    fn foo(&'a self) -> &'a i32 { &self.val }
}

fn main() {
    let s = S {
        val: 42
    };
    assert!(*s.foo() > 0);
}