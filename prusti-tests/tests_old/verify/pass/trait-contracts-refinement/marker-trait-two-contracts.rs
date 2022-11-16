use prusti_contracts::*;

trait Foo {
    fn foo(&self, arg: i32) -> bool;
}

trait Bar {
    fn bar(&self, arg: i32) -> bool;
}

#[refine_requires(Foo::foo = "arg > 0")]
#[refine_ensures(Foo::foo = "result == (arg > 5)")]
#[refine_requires(Bar::bar = "arg < 0")]
#[refine_ensures(Bar::bar = "result == (arg < -42)")]
trait Sub: Foo + Bar {}

struct Dummy { }

impl Foo for Dummy {
    fn foo(&self, arg: i32) -> bool {
        arg > 5
    }
}

impl Bar for Dummy {
    fn bar(&self, arg: i32) -> bool {
        arg < -42
    }
}

impl Sub for Dummy { }

fn test_foo(d: &Dummy) {
    assert!(d.foo(6));
    assert!(d.bar(-55));
}

fn main() {}
