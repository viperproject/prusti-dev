use prusti_contracts::*;

trait MyTrait {
    predicate! {
        fn foo(&self) -> bool;
    }
}

struct MyStruct;

#[refine_trait_spec]
impl MyTrait for MyStruct {
    predicate! {
        fn foo(&self) -> bool {
            true
        }
    }
}

impl MyStruct {
    predicate! {
        fn bar(&self) -> bool {
            true
        }
    }
}

fn main() {
    let s = MyStruct;
    MyTrait::foo(&s);
    s.foo();
    MyStruct::bar(&s);
    s.bar();
}
