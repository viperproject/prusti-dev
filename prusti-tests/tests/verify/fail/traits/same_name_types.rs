// Distinct items with the same path up to disambiguators (as `bitflags!`
// generates, one per `const _` block) must get distinct Viper identities:
// - `Inner`: encoded as one type, its two impls equate `Named::Tag` of it
//   with both `u8` and `u16`, making every obligation vacuously provable
//   (silently, as nothing else gives the collision away);
// - `Made`: additionally, its two `make` methods would be two Viper methods
//   of the same name.

use prusti_contracts::*;

pub trait Named {
    type Tag;
}

pub trait Make {
    fn make() -> Self;
}

pub fn tag<T: Named>(_t: T) {}

pub struct A;
pub struct B;

const _: () = {
    pub struct Inner;
    impl Named for Inner {
        type Tag = u8;
    }

    pub struct Made;
    impl Make for Made {
        fn make() -> Self {
            Made
        }
    }

    impl A {
        pub fn run(&self) {
            tag(Inner);
            let _ = Made::make();
        }
    }
};

const _: () = {
    pub struct Inner;
    impl Named for Inner {
        type Tag = u16;
    }

    pub struct Made;
    impl Make for Made {
        fn make() -> Self {
            Made
        }
    }

    impl B {
        pub fn run(&self) {
            tag(Inner);
            let _ = Made::make();
        }
    }
};

#[ensures(false)] //~ ERROR: postcondition might not hold
pub fn canary() {}
