use prusti_contracts::*;

trait SomeTrait {
    fn foo(x: i32) -> i32;
}
struct SomeStruct;
#[refine_trait_spec]
impl SomeTrait for SomeStruct {
    #[requires(false)] //~ ERROR
    fn foo(x: i32) -> i32 {
        panic!()
    }
}

fn main() {}