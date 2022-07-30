extern crate prusti_contracts;
use prusti_contracts::*;
trait SomeTrait {
    fn foo(x: i32) -> i32; //~ ERROR
}
struct SomeStruct;
#[refine_trait_spec]
impl SomeTrait for SomeStruct {
    #[requires(false)] //~ ERROR
    fn foo(x: i32) -> i32 {
        panic!()
    }
}
