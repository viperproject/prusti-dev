// compile-flags: -Penable_ghost_constraints=true
use prusti_contracts::*;

trait A {
    type AssocType;
}

trait SomeTrait {
    type AssocType;
    fn foo(&self) -> i32;
}

struct Foo<T> {
    x: T
}
impl<T> A for Foo<T> {
    type AssocType = i32;
}
impl<T> SomeTrait for Foo<T> {
    type AssocType = T;

    fn foo(&self) -> i32 {
        42
    }
}

#[extern_spec]
trait SomeTrait {
    #[ghost_constraint(Self: A<AssocType = <Self as SomeTrait>::AssocType> , [
    ensures(result > 0)
    ])]
    fn foo(&self) -> i32;
}

fn main() {
    let f = Foo {
        x: 42 as u32
    };
    let res = f.foo();
    assert!(res > 0); //~ ERROR: [Prusti: verification error] the asserted expression might not hold
}