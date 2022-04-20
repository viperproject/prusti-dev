#[allow(dead_code)]
use prusti_contracts::*;

trait SomeTrait {
    predicate! {
        fn foo(&self) -> bool;
    }
}

struct SomeStruct;
#[refine_trait_spec]
impl SomeTrait for SomeStruct {
    predicate! {
        fn foo(&self) -> bool {
            true
        }
    }
}

struct SomeOtherStruct<T: SomeTrait> {
    x: T,
}
impl<T: SomeTrait> SomeOtherStruct<T> {
    fn bar(&self) {
        self.x.foo();
    }
}

fn bar<T: SomeTrait>(x: T) {
    x.foo();
}

fn main() {
    let s = SomeStruct;
    assert!(s.foo());
}