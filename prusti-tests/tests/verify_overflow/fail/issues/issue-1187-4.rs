// compile-flags: -Popt_in_verification=true -Penable_type_invariants=true
use prusti_contracts::*;

fn main() {}

#[derive(Copy, Clone)]
#[invariant(self.bar > 0)]
pub struct Foo {
    pub bar: usize,
}

impl Foo {
    #[verified]
    pub const fn new(bar: usize) -> Self {
        //~^ ERROR type invariants might not hold
        Self { bar }
    }
}
