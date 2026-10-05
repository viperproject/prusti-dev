// An opt-out impl (`impl !Auto for X`) states that an auto trait is *not*
// implemented. Encoding it like a positive impl would make the blanket impls
// below apply to `X` alongside the concrete ones, resolving `<X as Foo>::A`
// to both `u32` and `u64` (which the canary detects).

#![feature(auto_traits, negative_impls, with_negative_coherence)]

use prusti_contracts::*;

// A user-defined auto trait.
mod user_auto_trait {
    pub auto trait Marker {}

    pub struct Out;
    impl !Marker for Out {}

    pub trait Foo {
        type A;
    }
    impl<T: Marker> Foo for T {
        type A = u32;
    }
    impl Foo for Out {
        type A = u64;
    }

    pub fn foo<T: Foo>(_t: T) {}

    pub fn use_out(x: Out) {
        foo(x);
    }
}

// A std auto trait.
mod send {
    pub struct NotSend;
    impl !Send for NotSend {}

    pub trait Foo {
        type A;
    }
    impl<T: Send> Foo for T {
        type A = u32;
    }
    impl Foo for NotSend {
        type A = u64;
    }

    pub fn foo<T: Foo>(_t: T) {}

    pub fn use_not_send(x: NotSend) {
        foo(x);
    }
}

#[ensures(false)] //~ ERROR: postcondition might not hold
pub fn canary() {}
