// A blanket impl and a more specific impl of the same trait coexist when the
// blanket impl's where-clauses rule out the specific impl's types. The
// blanket impl's associated types and method specifications must only be
// assumed where those where-clauses hold: otherwise both impls describe the
// same trait ref, their associated types resolve it to two distinct types
// (making the whole program inconsistent, which the canary detects) and
// their specifications describe the same call.

use prusti_contracts::*;

// `impl<T, U> TryFrom<U> for T where U: Into<T>` (`Error = Infallible`) and
// `impl TryFrom<u64> for usize` (`Error = TryFromIntError`), kept apart by
// `u64: Into<usize>` not holding.
mod try_from {
    use std::convert::TryFrom;

    pub fn narrow(x: u64) -> usize {
        match usize::try_from(x) {
            Ok(v) => v,
            Err(_) => 0,
        }
    }
}

// `impl<F: FnMut(char) -> bool> Pattern for F` and `impl Pattern for char`,
// kept apart by `char` not being `FnMut(char) -> bool`.
//
// Known incompleteness: the `Fn*` traits are implemented for closures by the
// compiler rather than by impls, so a closure's `FnMut` bound cannot be
// proven and the blanket impl's `Searcher` does not resolve for closure
// patterns.
mod pattern {
    pub fn first_word(s: &str) -> Option<&str> {
        s.split(' ').next()
    }
}

// `impl<T: Clone> ToOwned for T` (`Owned = T`) and `impl ToOwned for str`
// (`Owned = String`), kept apart by `str` being neither `Clone` nor `Sized`.
mod to_owned {
    pub fn owned() -> String {
        "x".to_owned()
    }
}

// `impl<I: Iterator> IntoIterator for I` (`IntoIter = I`) and a concrete
// `IntoIterator` impl, kept apart by the concrete type not being an
// `Iterator`.
mod into_iter {
    pub struct Bag(u32);
    pub struct BagIter(u32);

    impl Iterator for BagIter {
        type Item = u32;
        fn next(&mut self) -> Option<u32> {
            None
        }
    }

    impl IntoIterator for Bag {
        type Item = u32;
        type IntoIter = BagIter;
        fn into_iter(self) -> BagIter {
            BagIter(self.0)
        }
    }

    pub fn use_both(b: Bag, i: BagIter) {
        let _ = b.into_iter();
        let _ = i.into_iter();
    }
}

// A user-defined pair, kept apart only by the blanket impl's bound
// (`X: MyBound` does not hold).
mod user {
    pub trait MyBound {}
    pub trait Tr<U> {
        type Out;
    }

    pub struct S;
    pub struct X;
    pub struct Y;

    impl<U: MyBound> Tr<U> for S {
        type Out = U;
    }
    impl Tr<X> for S {
        type Out = Y;
    }

    pub fn out_x<T: Tr<X>>(_t: &T) {}

    pub fn use_x() {
        out_x(&S);
    }
}

// The only bound keeping the blanket impl apart from the impl for an unsized
// type is the implicit `T: Sized`, so the encoding must not consider `[u8]`
// sized.
mod sized {
    pub trait Tagged {
        type Tag;
    }

    impl<T> Tagged for T {
        type Tag = u32;
    }
    impl Tagged for [u8] {
        type Tag = u64;
    }

    pub fn tag<T: Tagged + ?Sized>(_t: &T) {}

    pub fn use_slice(s: &[u8]) {
        tag(s);
    }
}

// Method specifications: at `X`, both the blanket impl's `result == 1` and
// the concrete impl's `result == 2` would describe the call.
mod fn_spec {
    use prusti_contracts::*;

    pub trait MyBound {}
    pub trait Get {
        #[pure]
        fn get(&self) -> u32;
    }

    pub struct X;

    #[refine_trait_spec]
    impl<T: MyBound> Get for T {
        #[pure]
        #[ensures(result == 1)]
        fn get(&self) -> u32 {
            1
        }
    }
    #[refine_trait_spec]
    impl Get for X {
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
    pub fn use_x(x: &X) -> u32 {
        get_it(x)
    }
}

#[ensures(false)] //~ ERROR: postcondition might not hold
pub fn canary() {}
