use prusti_contracts::*;

trait MyTrait {
    #[ensures(result > 10)]
    fn foo(&self) -> i32;
}

struct MyStruct;

#[refine_trait_spec]
impl MyTrait for MyStruct {
    #[ensures(result > 5)]
    fn foo(&self) -> i32 {
        6
    }
}

fn main() {
}