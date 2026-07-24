//! A `#[refine_trait_spec]` implementation may strengthen the trait method's
//! specification. Here the impl keeps the method `#[pure]` (as required to
//! refine a pure trait method) and adds a postcondition, which callers can then
//! rely on.

use prusti_contracts::*;

trait Trait {
    #[pure]
    fn foo(&self) -> i32;
}

struct Struct(i32);

#[refine_trait_spec]
impl Trait for Struct {
    #[pure]
    #[ensures(result == self.0)]
    fn foo(&self) -> i32 {
        self.0
    }
}

fn client(s: &Struct) {
    // Relies on the refined postcondition of `foo`.
    assert!(s.foo() == s.0);
}
