// Auto trait bounds that guard an impl are discharged by explicit positive
// impls of the auto trait, and in generic code by the function's own bounds.
// Opt-out impls are not assumed (see `verify/fail/traits/auto_traits.rs`).
//
// Known incompleteness: an auto trait implemented structurally, without an
// impl (e.g. `struct S(u8)` is `Send`), is not known to hold, so the impls
// below do not resolve at `Wrap<S>`.

#![feature(auto_traits, negative_impls)]

use prusti_contracts::*;

pub struct Wrap<T>(pub T);

pub fn get<T: Tr>(_t: &T) -> Option<T::A> {
    None
}

pub trait Tr {
    type A;
}
impl<T: Send> Tr for Wrap<T> {
    type A = u8;
}

// A raw pointer field opts out of `Send`; the explicit impl opts back in.
pub struct Explicit(pub *const u8);
unsafe impl Send for Explicit {}

pub fn explicit(w: &Wrap<Explicit>) -> Option<u8> {
    get(w)
}

pub fn generic<T: Send>(w: &Wrap<T>) -> Option<u8> {
    get(w)
}

mod user_auto_trait {
    pub auto trait Marker {}

    pub struct Out;
    impl !Marker for Out {}

    // Contains an opted-out field; the explicit impl opts back in.
    pub struct Contains(pub Out);
    impl Marker for Contains {}

    pub struct Wrap<T>(pub T);
    pub trait Tr {
        type A;
    }
    impl<T: Marker> Tr for Wrap<T> {
        type A = u8;
    }

    pub fn get<T: Tr>(_t: &T) -> Option<T::A> {
        None
    }

    pub fn explicit(w: &Wrap<Contains>) -> Option<u8> {
        get(w)
    }

    pub fn generic<T: Marker>(w: &Wrap<T>) -> Option<u8> {
        get(w)
    }
}
