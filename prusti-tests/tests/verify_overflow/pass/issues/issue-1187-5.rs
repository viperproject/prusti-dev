// compile-flags: -Popt_in_verification=true
use prusti_contracts::*;

fn main() {}

predicate! {
    fn baz(foo: &Foo) -> bool {
        foo.bar > 0
    }
}

#[derive(Copy, Clone)]
pub struct Foo {
    pub bar: usize,
}

impl Foo {
    #[verified]
    #[pure]
    #[ensures(match result {
        Some(foo) => baz(&foo),
        None => true,
    })]
    pub const fn new(bar: usize) -> Option<Self> {
        if bar > 0 {
            Some(Self { bar })
        } else {
            None
        }
    }
}
