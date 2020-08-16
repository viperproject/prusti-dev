#![feature(register_tool)]
#![register_tool(prusti)]

#[trait_invariant(self.d1 == self.d2)] // not yet implemented
trait Foo {}

struct Dummy {
    d1: i32,
    d2: i32,
}

impl Foo for Dummy { }

fn test_dummy(d: &Dummy) {
    assert!(d.d1 == d.d2);
}

fn main() { }
