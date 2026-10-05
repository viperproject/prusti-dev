// With specialization, a `default` item (or anything a partial `default impl`
// provides) may be overridden where its impl applies, also by impls in crates
// this one cannot see. Such definitions are only assumed where a final impl
// inherits them (see `verify/pass/traits/specialization.rs` for what still
// resolves).

#![feature(specialization)]
#![allow(incomplete_features)]

use prusti_contracts::*;

// A `default` method specification: at `u8`, both `result == 1` and
// `result == 2` would describe the call.
mod fn_spec {
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

    #[pure]
    pub fn get_it<T: Get>(t: &T) -> u32 {
        t.get()
    }

    #[ensures(false)] //~ ERROR: postcondition might not hold
    pub fn use_u8(x: &u8) -> u32 {
        get_it(x)
    }

    pub fn wrong_u8(x: &u8) {
        prusti_assert!(get_it(x) == 1); //~ ERROR: assertion might not hold
    }
}

// A `default type`: `<u8 as Tagged>::Tag` would be both `u32` and `u64`,
// making the whole program inconsistent (which the canary detects).
mod assoc_type {
    pub trait Tagged {
        type Tag;
    }
    impl<T> Tagged for T {
        default type Tag = u32;
    }
    impl Tagged for u8 {
        type Tag = u64;
    }

    pub fn tag<T: Tagged>(_t: T) {}

    pub fn use_u8(x: u8) {
        tag(x);
    }
}

// A default body inherited by a partial `default impl` is specializable like
// a `default` item: it is not assumed from that impl (`u8` overrides it), but
// it still is for a final impl that inherits it (`u16`).
mod inherited_default {
    use prusti_contracts::*;

    pub trait Tr {
        #[pure]
        fn f(&self) -> u32 {
            1
        }
    }

    default impl<T> Tr for T {}

    #[refine_trait_spec]
    impl Tr for u8 {
        #[pure]
        fn f(&self) -> u32 {
            2
        }
    }

    impl Tr for u16 {}

    #[pure]
    pub fn f_of<T: Tr>(t: &T) -> u32 {
        t.f()
    }

    #[ensures(false)] //~ ERROR: postcondition might not hold
    pub fn use_u8(x: &u8) -> u32 {
        f_of(x)
    }

    pub fn resolved(x: &u8, y: &u16) {
        prusti_assert!(f_of(x) == 2);
        prusti_assert!(f_of(y) == 1);
    }
}

// Items a partial `default impl` provides are assumed only where a final impl
// inherits them (`u16`), not where another impl overrides them (`u8`): there,
// `<u8 as Tagged>::Tag` would be both `u32` and `u64` (which the canary
// detects), and `get` both `1` and `2`.
mod inherited_items {
    use prusti_contracts::*;

    pub trait Tagged {
        type Tag;
        #[pure]
        fn get(&self) -> u32;
    }

    #[refine_trait_spec]
    default impl<T> Tagged for T {
        type Tag = u32;
        #[pure]
        #[ensures(result == 1)]
        fn get(&self) -> u32 {
            1
        }
    }
    #[refine_trait_spec]
    impl Tagged for u8 {
        type Tag = u64;
        #[pure]
        #[ensures(result == 2)]
        fn get(&self) -> u32 {
            2
        }
    }
    impl Tagged for u16 {}

    #[pure]
    pub fn get_it<T: Tagged>(t: &T) -> u32 {
        t.get()
    }

    pub fn tag<T: Tagged>(_t: T) -> Option<T::Tag> {
        None
    }

    pub fn use_both(x: u8, y: u16) -> (Option<u64>, Option<u32>) {
        (tag(x), tag(y))
    }

    #[ensures(false)] //~ ERROR: postcondition might not hold
    pub fn use_u8(x: &u8) -> u32 {
        get_it(x)
    }

    pub fn resolved(x: &u8, y: &u16) {
        prusti_assert!(get_it(x) == 2);
        prusti_assert!(get_it(y) == 1);
    }
}

// Even with no specialization of `get` here, a downstream crate may add
// `impl Get for Local { fn get(&self) -> u32 { 2 } }` and call
// `generic::<Local>`, so the default is not assumed.
mod opaque {
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

    #[pure]
    pub fn via<T>(t: &T) -> u32 {
        t.get()
    }

    #[ensures(result == 1)] //~ ERROR: postcondition might not hold
    pub fn generic<T>(t: &T) -> u32 {
        via(t)
    }
}

#[ensures(false)] //~ ERROR: postcondition might not hold
pub fn canary() {}
