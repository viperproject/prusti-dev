use prusti_contracts::*;

trait SomeTrait {
    predicate! {
        fn foo(&self) -> i32;
    }
}

struct SomeStruct;

#[refine_trait_spec]
impl SomeTrait for SomeStruct {
    predicate! {
        fn foo(&self) -> i32 {
            42 //~ ERROR: mismatched types
        }
    }
}

fn main() {

}