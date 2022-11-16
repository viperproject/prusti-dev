use prusti_contracts::*;

#[invariant(self.d1 == self.d2)]
trait Foo {}

struct Dummy<T> {
    d1: T,
    d2: T,
}

impl Foo for Dummy<i32> { }

fn test_dummy(d: &Dummy<i32>) {
    assert!(d.d1 == d.d2);
}

fn main() { }
