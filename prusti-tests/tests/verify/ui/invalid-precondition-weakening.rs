use prusti_contracts::*;

trait MyTrait {
    #[requires(x > 10)]
    #[requires(y > 15)]
    fn foo(&self, x: i32, y: i32) -> i32;
}

struct MyStruct {
}

#[refine_trait_spec]
impl MyTrait for MyStruct {

    #[requires(x > 15)]
    #[requires(y > 20)]
    fn foo(&self, x: i32, y: i32) -> i32 {
        x + y + 42
    }
}

fn main() {
}