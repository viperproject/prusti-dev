use prusti_contracts::*;

trait MyTrait {
    predicate! {
        fn foo(&self) -> i32;
    }
}

struct MyStruct;

#[refine_trait_spec]
impl MyTrait for MyStruct {
    fn foo(&self) -> i32 {
        42
    }
}

fn main() {
}