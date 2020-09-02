extern crate prusti_contracts;

#[invariant="self.d1 > 5"] //~ ERROR mismatched types
trait Foo { }

struct Dummy {
    d1: bool
}

impl Foo for Dummy {}

fn main() { }
