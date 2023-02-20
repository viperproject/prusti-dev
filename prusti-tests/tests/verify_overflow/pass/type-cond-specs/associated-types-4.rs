use prusti_contracts::*;

trait A {
    type AssocType;
}

trait SomeTrait<T> {
    type AssocType;
    fn foo(&self, x: T) -> i32;
}

struct Foo;
impl A for Foo {
    type AssocType = i32;
}
impl<T> SomeTrait<T> for Foo {
    type AssocType = T;

    fn foo(&self, x: T) -> i32 {
        42
    }
}

#[extern_spec]
trait SomeTrait<T> {
    #[refine_spec(where Self: A<AssocType = <Self as SomeTrait<T>>::AssocType>, [
        ensures(result > 0)
    ])]
    fn foo(&self, x: T) -> i32;
}

fn main() {
    let f = Foo;
    let res = f.foo(42 as i32);
    assert!(res > 0);
}
