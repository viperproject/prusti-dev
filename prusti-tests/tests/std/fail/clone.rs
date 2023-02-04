#![feature(negative_impls)]
//~^ ERROR: postcondition might not hold
// the above error is currently reported with an incorrect span due to issue #1310.
// it should be down on line 38 at the actual implementation.

use prusti_contracts::*;

fn main() {}

#[derive(Clone)]
struct Foo {
    x: i32,
}

impl !core_spec::SnapshotEqualClone for Foo {}

fn foo() {
    let foo = Foo { x: 1 };
    assert!(foo.clone().x == 1); //~ ERROR: the asserted expression might not hold
}

#[derive(Clone)]
struct FooHolder {
    foo: Foo,
}

fn foo_holder() {
    let foo = Foo { x: 1 };
    let holder = FooHolder { foo };
    assert!(holder.clone().foo.x == 1); //~ ERROR: the asserted expression might not hold
}

struct Bar {
    x: i32,
}

impl Clone for Bar {
    fn clone(&self) -> Self {
        Self { x: self.x + 1 }
    }
}

fn bar() {
    let bar = Bar { x: 2 };
    assert!(bar.clone().x == 2);
}
