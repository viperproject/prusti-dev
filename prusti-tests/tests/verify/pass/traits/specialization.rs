// With specialization, a `default` item (or anything a partial `default impl`
// provides) is only assumed where a final impl inherits it, since elsewhere a
// specializing impl, possibly in another crate, may override it (see
// `verify/fail/traits/specialization.rs`). The final definitions of
// specializing impls still resolve at their trait refs.
//
// Known incompleteness: the root's `default fn get` is not assumed even where
// it is the definition Rust uses, e.g. `get_it(&0u16)` is unknown.

#![feature(specialization)]
#![allow(incomplete_features)]

use prusti_contracts::*;

pub trait Get {
    #[pure]
    fn get(&self) -> u32;
}

#[refine_trait_spec]
impl<T> Get for T {
    #[pure]
    #[ensures(result == 1)]
    default fn get(&self) -> u32 {
        1
    }
}
#[refine_trait_spec]
impl Get for u8 {
    #[pure]
    #[ensures(result == 2)]
    fn get(&self) -> u32 {
        2
    }
}
// A repeated parameter: only pairs of equal types.
#[refine_trait_spec]
impl<T> Get for (T, T) {
    #[pure]
    #[ensures(result == 3)]
    fn get(&self) -> u32 {
        3
    }
}
// A const pattern.
#[refine_trait_spec]
impl Get for [u8; 2] {
    #[pure]
    #[ensures(result == 4)]
    fn get(&self) -> u32 {
        4
    }
}
// A partial impl that inherits `get`, specialized further by an impl that
// overrides it.
default impl<T> Get for Vec<T> {}
#[refine_trait_spec]
impl Get for Vec<u16> {
    #[pure]
    #[ensures(result == 5)]
    fn get(&self) -> u32 {
        5
    }
}

#[pure]
pub fn get_it<T: Get>(t: &T) -> u32 {
    t.get()
}

pub fn specialized(x: &u8, p: &(u16, u16), a: &[u8; 2], v: &Vec<u16>) {
    prusti_assert!(get_it(x) == 2);
    prusti_assert!(get_it(p) == 3);
    prusti_assert!(get_it(a) == 4);
    prusti_assert!(get_it(v) == 5);
}

// A final impl that does not mention an item finalizes the definition it
// inherits from the impl it specializes (E0520), so that definition resolves
// at the final impl's trait refs.
mod inherited_from_default_impl {
    use prusti_contracts::*;

    pub trait Tr {
        type A;
        #[pure]
        fn f(&self) -> u32;
    }

    #[refine_trait_spec]
    default impl<T> Tr for T {
        type A = u32;
        #[pure]
        #[ensures(result == 1)]
        fn f(&self) -> u32 {
            1
        }
    }
    impl Tr for u16 {}

    #[pure]
    pub fn f_of<T: Tr>(t: &T) -> u32 {
        t.f()
    }

    pub fn tag<T: Tr>(_t: T) -> Option<T::A> {
        None
    }

    pub fn user(x: &u16) {
        prusti_assert!(f_of(x) == 1);
    }

    pub fn resolves(x: u16) -> Option<u32> {
        tag(x)
    }
}

mod inherited_default_item {
    use prusti_contracts::*;

    pub trait Tr {
        type A;
        #[pure]
        fn f(&self) -> u32;
    }

    #[refine_trait_spec]
    impl<T> Tr for T {
        default type A = u32;
        #[pure]
        #[ensures(result == 1)]
        default fn f(&self) -> u32 {
            1
        }
    }
    impl Tr for u16 {}

    #[pure]
    pub fn f_of<T: Tr>(t: &T) -> u32 {
        t.f()
    }

    pub fn tag<T: Tr>(_t: T) -> Option<T::A> {
        None
    }

    pub fn user(x: &u16) {
        prusti_assert!(f_of(x) == 1);
    }

    pub fn resolves(x: u16) -> Option<u32> {
        tag(x)
    }
}
