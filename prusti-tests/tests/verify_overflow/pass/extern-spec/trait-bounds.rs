// ignore-test fails because of const generics
use prusti_contracts::*;

struct Foo<'a, T: PartialEq, const L: usize>(&'a [T; L]);

impl<'a, T: PartialEq, const L: usize> Foo<'a, T, L> {
    pub fn bar(self) -> &'a [T; L] { self.0 }
}

#[extern_spec]
impl<'a, T: PartialEq, const L: usize> Foo<'a, T, L> {
    #[pure]
    #[ensures(result == self.0)]
    pub fn bar(self) -> &'a [T; L];
}

fn main() {}
