use prusti_contracts::*;

trait MyTrait {
    #[pure]
    fn foo(&self) -> i32;
}

struct MyStruct;

#[refine_trait_spec]
impl MyTrait for MyStruct {
    #[ensures(result > 0)]
    fn foo(&self) -> i32 {
        42
    }
}

fn main() {
    let s = MyStruct;
    s.foo();
}