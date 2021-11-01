// compile-flags: -Pprint_desugared_specs=true -Pprint_typeckd_specs=true -Phide_uuids=true -Pno_verify=true
// normalize-stdout-test: "[a-z0-9]{32}" -> "$(NUM_UUID)"
// normalize-stdout-test: "[a-z0-9]{8}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{12}" -> "$(UUID)"
// normalize-stdout-test: "\[[a-z0-9]{4}\]::" -> "[$(CRATE_ID)]::"

extern crate prusti_contracts;
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
