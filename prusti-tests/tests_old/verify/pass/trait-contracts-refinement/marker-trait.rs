use prusti_contracts::*;

trait Foo {
    fn foo(&self) -> bool;
}

#[refine_ensures(Foo::foo = "result")]
trait Sub: Foo {}

struct Dummy { }

impl Foo for Dummy {
    fn foo(&self) -> bool {
        true
    }
}

impl Sub for Dummy { }

fn test_foo(d: &Dummy) {
    assert!(d.foo());
}

fn main() {}
