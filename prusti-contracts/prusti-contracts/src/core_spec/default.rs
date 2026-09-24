use crate::*;

use core::default::Default;

// TODO: this should ideally be `#[refine_spec(where Self: PureDefault, [pure])]`
// (cf. `PartialEq::eq`), since not every `Default::default` is pure.
#[extern_spec]
trait Default: Sized {
    #[trusted]
    #[pure]
    fn default() -> Self;
}

macro_rules! default_spec {
    ($($t:ty => $v:expr),* $(,)?) => {$(
        #[extern_spec]
        impl Default for $t {
            #[trusted]
            #[pure]
            #[ensures(result == $v)]
            fn default() -> $t;
        }
    )*}
}

default_spec!(
    i8 => 0, i16 => 0, i32 => 0, i64 => 0, i128 => 0, isize => 0,
    u8 => 0, u16 => 0, u32 => 0, u64 => 0, u128 => 0, usize => 0,
    f32 => 0.0, f64 => 0.0,
    bool => false, char => '\0', () => (),
);

#[extern_spec]
impl<T> Default for Option<T> {
    #[trusted]
    #[pure]
    #[ensures(matches!(result, None))]
    fn default() -> Option<T>;
}

#[extern_spec]
impl<'a, T> Default for &'a [T] {
    #[trusted]
    #[pure]
    #[ensures(result.len() == 0)]
    fn default() -> &'a [T];
}

// The default of a tuple is the tuple of the defaults. Written out per arity:
// the `===` operator does not survive a `macro_rules!` expansion (its three
// `=` are no longer joint tokens).
#[extern_spec]
impl<A: Default> Default for (A,) {
    #[trusted]
    #[pure]
    #[ensures(result.0 === A::default())]
    fn default() -> (A,);
}

#[extern_spec]
impl<A: Default, B: Default> Default for (A, B) {
    #[trusted]
    #[pure]
    #[ensures(result.0 === A::default() && result.1 === B::default())]
    fn default() -> (A, B);
}

#[extern_spec]
impl<A: Default, B: Default, C: Default> Default for (A, B, C) {
    #[trusted]
    #[pure]
    #[ensures(result.0 === A::default() && result.1 === B::default() && result.2 === C::default())]
    fn default() -> (A, B, C);
}

#[extern_spec]
impl<A: Default, B: Default, C: Default, D: Default> Default for (A, B, C, D) {
    #[trusted]
    #[pure]
    #[ensures(result.0 === A::default()
        && result.1 === B::default()
        && result.2 === C::default()
        && result.3 === D::default())]
    fn default() -> (A, B, C, D);
}
