// A trait fn's default body describes the impls that inherit it; an impl may
// override it with a different result (see
// `verify/fail/traits/default_bodies.rs`).

use prusti_contracts::*;

pub trait Tr {
    #[pure]
    #[ensures(result > 0)]
    fn f(&self) -> u32 {
        1
    }

    #[pure]
    fn g(&self) -> u32 {
        self.f() + 1
    }

    #[pure]
    fn h<U: Copy>(&self, u: U) -> U {
        u
    }
}

pub struct Over;
pub struct Inherit;

#[refine_trait_spec]
impl Tr for Over {
    #[pure]
    #[ensures(result == 5)]
    fn f(&self) -> u32 {
        5
    }
}
impl Tr for Inherit {}
impl Tr for Vec<u8> {}

#[pure]
pub fn f_of<T: Tr>(t: &T) -> u32 {
    t.f()
}

#[pure]
pub fn g_of<T: Tr>(t: &T) -> u32 {
    t.g()
}

#[pure]
pub fn h_of<T: Tr>(t: &T, x: u32) -> u32 {
    t.h(x)
}

pub fn overriding(o: &Over) {
    prusti_assert!(f_of(o) == 5);
    // The inherited `g` calls the overriding `f`.
    prusti_assert!(g_of(o) == 6);
}

pub fn inheriting(i: &Inherit, v: &Vec<u8>) {
    prusti_assert!(f_of(i) == 1);
    prusti_assert!(g_of(i) == 2);
    prusti_assert!(h_of(i, 7) == 7);
    prusti_assert!(f_of(v) == 1);
}

// Generic callers get the trait's contract.
#[ensures(result > 0)]
pub fn generic<T: Tr>(t: &T) -> u32 {
    f_of(t)
}
