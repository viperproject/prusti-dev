use prusti_contracts::*;

trait SomeTrait {
    fn foo(x: i32) -> bool;
}
struct SomeStruct;
#[refine_trait_spec]
impl SomeTrait for SomeStruct {
    predicate! {
        fn foo(x: i32) -> bool { //~ ERROR
            true
        }
    }
}

fn main() {}
