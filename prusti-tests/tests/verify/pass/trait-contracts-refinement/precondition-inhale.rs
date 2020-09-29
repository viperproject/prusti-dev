use prusti_contracts::*;

trait Foo {
    #[requires(_val > 100)]
    fn foo(&self, _val: i32);
}

struct Dummy { }

#[refine_trait_spec]
impl Foo for Dummy {
    #[requires(_val > 12)]
    fn foo(&self, _val: i32) { }
}

fn main() {
    let d = Dummy {};
    d.foo(42);
}

