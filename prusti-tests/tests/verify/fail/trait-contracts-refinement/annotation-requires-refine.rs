//! Prusti annotations on a trait implementation are only allowed if the `impl`
//! block is marked `#[refine_trait_spec]`. Otherwise the annotation would
//! silently fail to refine the inherited trait specification, so it is rejected.

use prusti_contracts::*;

trait Trait {
    #[pure]
    fn foo(&self) -> i32;
}

struct Struct;

impl Trait for Struct {
    #[trusted] //~ ERROR: Prusti annotations on a trait implementation require the `#[refine_trait_spec]` attribute on the `impl` block
    fn foo(&self) -> i32 {
        5
    }
}
