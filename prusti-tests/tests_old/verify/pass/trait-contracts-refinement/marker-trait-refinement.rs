use prusti_contracts::*;

trait Foo {
    #[ensures(result > 42)]
    fn foo(&self) -> i32;
}

#[refine_ensures(Foo::foo = "result < 442")]
trait Sub: Foo {}

struct Dummy { }

impl Foo for Dummy {
    fn foo(&self) -> i32 {
        84
    }
}

impl Sub for Dummy { }

fn test_foo(d: &Dummy) {
    assert!(d.foo() > 0);
    assert!(d.foo() < 1000);
}

fn main() {}
