extern crate prusti_contracts;

#[invariant="self.d1 == self.d2"]
trait Foo { }

struct Dummy where {
    d1: i32,
    d2: i32,
}

impl Foo for Dummy { }

type Bar = Dummy;

fn test_dummy(d: &Bar) {
    assert!(d.d1 == d.d2);
}

fn main() { }
