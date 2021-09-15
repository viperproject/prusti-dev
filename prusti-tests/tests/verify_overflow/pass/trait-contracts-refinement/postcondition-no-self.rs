use prusti_contracts::*;


trait Foo {
    #[ensures(result > 0)]
    fn foo(_a: i32) -> i32;
}

struct Dummy { }

#[refine_trait_spec]
impl Foo for Dummy {
    #[ensures(result == 5)]
    fn foo(_a: i32) -> i32 {
        5
    }
}

fn main() {
    let val = Dummy::foo(3);
    assert!(val == 5);
}
