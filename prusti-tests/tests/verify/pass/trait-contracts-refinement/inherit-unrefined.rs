//! A trait implementation that is *not* marked `#[refine_trait_spec]` carries
//! no specification of its own and inherits the trait method's specification
//! wholesale. In particular it inherits the `#[pure]` kind, so the method stays
//! usable inside pure functions and specifications without repeating `#[pure]`.

use prusti_contracts::*;

trait Trait {
    #[pure]
    fn foo(&self) -> i32;
}

struct Struct;

// No `#[refine_trait_spec]` and no `#[pure]` here: both are inherited.
impl Trait for Struct {
    fn foo(&self) -> i32 {
        5
    }
}

// Usable in a pure function only because `foo` inherited `#[pure]`.
#[pure]
fn get(s: &Struct) -> i32 {
    s.foo()
}

// Usable in a specification for the same reason.
#[requires(s.foo() == 5)]
fn requires_foo(s: &Struct) {}
