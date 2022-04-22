use prusti_contracts::*;

trait A {
    #[pure]
    fn res(&self) -> i32 { 0 }
}

struct Foo;

#[refine_trait_spec]
impl A for Foo {
    #[pure]
    #[ensures(result == 42)]
    fn res(&self) -> i32 { 42 }
}

fn verify(foo: Foo) {
    assert!(foo.res() == 42);
}

fn main() {}
