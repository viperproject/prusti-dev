use prusti_contracts::*;

trait A {
    type AssocType;
}

trait SomeTrait {
    type AssocType;
    fn foo(&self) -> i32;
}

struct Foo;
impl A for Foo {
    type AssocType = i32;
}
impl SomeTrait for Foo {
    type AssocType = i32;

    fn foo(&self) -> i32 {
        42
    }
}

#[extern_spec]
trait SomeTrait {
    #[refine_spec(where Self: A<AssocType = <Self as SomeTrait>::AssocType> [
        ensures(result > 0)
    ])]
    fn foo(&self) -> i32;
}

fn main() {
    let f = Foo;
    let res = f.foo();
    assert!(res > 0); // Ghost constraint satisfied!
}
