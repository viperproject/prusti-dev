use prusti_contracts::*;

#[invariant(self.d1 > 5)] //~ ERROR mismatched types
trait Foo { }

struct Dummy<T> {
    d1: T
}

impl Foo for Dummy<String> {}

fn main() { }

