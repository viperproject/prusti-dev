use prusti_contracts::*;

trait MyTrait {
    fn foo() -> bool;
}

#[extern_spec]
trait MyTrait {
    predicate!{
        fn foo() -> bool;
    }
}

struct MyStruct;
impl MyStruct {
    fn bar() -> bool {
        true
    }
}

#[extern_spec]
impl MyStruct {
    predicate!{
        fn bar() -> bool;
    }
}

fn main() {}
