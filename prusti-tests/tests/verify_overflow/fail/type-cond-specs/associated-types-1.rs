use prusti_contracts::*;

trait A {
    type AssocType;
}

struct Foo;
impl A for Foo {
    type AssocType = i32;
}

#[trusted]
#[refine_spec(where T: A<AssocType = u32>, [
    ensures(result > 0)
])]
fn foo<T>(x: T) -> i32 {
    42
}


fn main() {
    let f = Foo;
    let res = foo(f);
    assert!(res > 0); //~ ERROR: the asserted expression might not hold
}
