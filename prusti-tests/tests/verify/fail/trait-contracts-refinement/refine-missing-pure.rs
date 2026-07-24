//! A `#[refine_trait_spec]` implementation takes over the specification of the
//! trait method it refines. If the trait method is `#[pure]` but the refining
//! implementation omits `#[pure]`, it would refine a pure method into an impure
//! one, which is rejected.

use prusti_contracts::*;

trait Trait {
    #[pure]
    fn foo(&self) -> i32;
}

struct Struct;

#[refine_trait_spec]
impl Trait for Struct {
    // Missing `#[pure]` while refining a pure trait method.
    #[ensures(result == 5)]
    fn foo(&self) -> i32 { //~ ERROR: implements a `#[pure]` trait method and so must itself be `#[pure]`
        5
    }
}
