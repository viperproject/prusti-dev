extern crate prusti_contracts;

// ignore-test There is a bug in the generics code generation.

#[invariant="self.d1 == self.d2"]
trait Foo {}

struct Dummy<T> {
    d1: T,
    d2: T,
}

impl<T> Foo for Dummy<T> where T: PartialEq { }

fn test_dummy(d: &Dummy<i32>) {
    assert!(d.d1 == d.d2);
}

fn main() { }
