use prusti_contracts::*;

trait SomeTrait {
    fn foo(x: &mut i32) -> &mut i32;
}
struct SomeStruct;
#[refine_trait_spec]
impl SomeTrait for SomeStruct {
    #[ensures(*result == old(*x))]
    #[after_expiry(before_expiry(*result) == *x)]
    fn foo(x: &mut i32) -> &mut i32 {
        x
    }
}

fn main() {}
