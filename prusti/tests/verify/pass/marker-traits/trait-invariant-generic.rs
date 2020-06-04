extern crate prusti_contracts;

// ignore-test Generics are not yet supported for marker trait implementations.

#[invariant="self.d1 == self.d2"]
trait Foo { }

struct Dummy<T> where T: PartialEq {
    d1: T,
    d2: T,
}

impl Foo for Dummy<i32> { }

fn test_dummy(d: &Dummy<i32>) {
    assert!(d.d1 == d.d2);
}

fn main() { }
