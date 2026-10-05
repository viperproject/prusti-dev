// An impl may weaken a trait method's precondition, and a call through it is
// then valid outside the trait's precondition. There the trait's
// postconditions are not promised: behavioural subtyping only relates the two
// where the trait's precondition holds.

use prusti_contracts::*;

pub struct X;

pub trait Pure {
    #[pure]
    #[requires(x > 0)]
    #[ensures(result > 0)]
    fn f(&self, x: u32) -> u32;
}

#[refine_trait_spec]
impl Pure for X {
    #[pure]
    #[requires(true)]
    #[ensures(result == x)]
    fn f(&self, x: u32) -> u32 {
        x
    }
}

#[ensures(false)] //~ ERROR: postcondition might not hold
pub fn pure_outside(t: &X) -> u32 {
    t.f(0)
}

pub trait Impure {
    #[requires(x > 0)]
    #[ensures(result > 0)]
    fn g(&self, x: u32) -> u32;
}

#[refine_trait_spec]
impl Impure for X {
    #[requires(true)]
    #[ensures(result == x)]
    fn g(&self, x: u32) -> u32 {
        x
    }
}

#[ensures(false)] //~ ERROR: postcondition might not hold
pub fn impure_outside(t: &X) -> u32 {
    t.g(0)
}
