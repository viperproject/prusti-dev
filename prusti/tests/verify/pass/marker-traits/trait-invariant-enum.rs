extern crate prusti_contracts;

// ignore-test Enumeration invariants on top level are not supported by Prusti atm.

#[invariant="match self {
    Self::Val(v) => v > 5,
    Self::Or(o) => o < 5
}"]
trait Foo { }

enum Dummy {
    Val(i32),
    Or(i32),
}

impl Foo for Dummy { }

fn test_dummy(d: Dummy) {
    match d {
        Dummy::Val(v) => assert!(v > 3),
        Dummy::Or(o) => assert!(o < 142),
    }
}

fn main() { }
