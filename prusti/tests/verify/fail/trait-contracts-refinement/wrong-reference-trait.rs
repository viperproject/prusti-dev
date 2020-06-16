extern crate prusti_contracts;

trait Foo {
    fn foo(&self, arg: i32) -> bool;
}

#[refine_requires(Bar::foo = "arg > 0")] //~ ERROR does not refer to super trait
trait Sub: Foo {}

struct Dummy { }

impl Foo for Dummy {
    fn foo(&self, arg: i32) -> bool {
        arg > 5
    }
}

impl Sub for Dummy { }

fn test_foo(d: &Dummy) {
    assert!(d.foo(6));
}

fn main() {}

