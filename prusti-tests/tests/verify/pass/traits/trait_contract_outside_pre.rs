// A trait's postconditions are promised where its precondition holds (see
// `verify/fail/traits/trait_contract_outside_pre.rs` for calls outside it):
// generic callers inside the precondition still get them, and calls outside
// it get the impl's contract. An impl that inherits a default body gets it.

use prusti_contracts::*;

pub struct X;
pub struct Y;

pub trait Tr {
    #[pure]
    #[requires(x > 0)]
    #[ensures(result > 0)]
    fn f(&self, x: u32) -> u32;

    #[pure]
    #[requires(x > 0)]
    fn h(&self, x: u32) -> u32 {
        let _ = x;
        1
    }
}

#[refine_trait_spec]
impl Tr for X {
    #[pure]
    #[requires(true)]
    #[ensures(result == x)]
    fn f(&self, x: u32) -> u32 {
        x
    }

    #[pure]
    #[requires(true)]
    fn h(&self, x: u32) -> u32 {
        if x > 0 { 1 } else { 2 }
    }
}

#[refine_trait_spec]
impl Tr for Y {
    #[pure]
    #[requires(x > 0)]
    #[ensures(result == 7)]
    fn f(&self, x: u32) -> u32 {
        let _ = x;
        7
    }
}

#[requires(x > 0)]
#[ensures(result > 0)]
pub fn generic_f<T: Tr>(t: &T, x: u32) -> u32 {
    t.f(x)
}

#[ensures(result == 0)]
pub fn outside_f(t: &X) -> u32 {
    t.f(0)
}

#[ensures(result == 2)]
pub fn outside_h(t: &X) -> u32 {
    t.h(0)
}

#[ensures(result == 1)]
pub fn inherited_h(t: &Y) -> u32 {
    t.h(3)
}
