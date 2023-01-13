use prusti_contracts::*;

trait A {}

trait MyTrait {
    #[ensures(result > 0)]
    #[refine_spec(where Self: A, [
        ensures(result % 2 == 0)
    ])]
    fn foo(&self) -> i32;
}

struct MyStruct;
#[refine_trait_spec]
impl MyTrait for MyStruct {

    #[ensures(result > 10)]
    #[refine_spec(where Self: A, [ //~ ERROR: Type-conditional spec refinements in trait spec refinements not supported
        ensures(result % 6 == 0)
    ])]
    fn foo(&self) -> i32 {
        42
    }
}

fn main() {
    // MyStruct does not implement A
    let s = MyStruct;
    assert!(s.foo() > 0);
}
