//! A `#[refine_trait_spec]` implementation must be a behavioral subtype of the
//! trait method it refines: its precondition may only be weaker (accept more)
//! and its postcondition only stronger (promise more). Here the implementation
//! does the opposite - a stronger precondition and a weaker postcondition - so
//! both are rejected.

use prusti_contracts::*;

trait Trait {
    #[requires(x > 1)]
    #[requires(x < 100)]
    #[ensures(result >= 0)]
    #[ensures(result < 99)]
    fn foo(&self, x: i32) -> i32;
}

struct Struct;

#[refine_trait_spec]
impl Trait for Struct {
    #[requires(x > 2)] //~ ERROR: the implementation's precondition may be stronger than the trait method's
    #[ensures(result >= 0)] //~ ERROR: the implementation's postcondition may be weaker than the trait method's
    #[ensures(result <= 99)]
    fn foo(&self, x: i32) -> i32 {
        10
    }
}
