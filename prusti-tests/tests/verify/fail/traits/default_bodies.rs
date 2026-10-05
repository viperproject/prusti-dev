// A trait fn's default body is not a promise about every implementation: an
// impl may override it with a different result.

use prusti_contracts::*;

pub trait Tr {
    #[pure]
    fn f(&self) -> u32 {
        1
    }
}

pub struct Over;

#[refine_trait_spec]
impl Tr for Over {
    #[pure]
    fn f(&self) -> u32 {
        2
    }
}

#[pure]
pub fn f_of<T: Tr>(t: &T) -> u32 {
    t.f()
}

#[ensures(result == 1)] //~ ERROR: postcondition might not hold
pub fn generic<T: Tr>(t: &T) -> u32 {
    f_of(t)
}

pub fn overriding(o: &Over) {
    prusti_assert!(f_of(o) == 1); //~ ERROR: assertion might not hold
}

#[ensures(false)] //~ ERROR: postcondition might not hold
pub fn canary() {}
