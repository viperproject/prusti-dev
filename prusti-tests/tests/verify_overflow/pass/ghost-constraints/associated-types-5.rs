// compile-flags: -Penable_ghost_constraints=true
use prusti_contracts::*;

trait A<T> {
    type AssocType;
}

struct Foo;
impl A<i32> for Foo {
    type AssocType = u32;
}

#[trusted]
#[ghost_constraint(T: A<i32, AssocType = u32> , [
ensures(result > 0)
])]
fn foo<T>(x: T) -> i32 {
    42
}

fn main() {
    let f = Foo;
    let res = foo(f);
    assert!(res > 0);
}