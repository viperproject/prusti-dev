use crate::*;

use core::{cmp::PartialEq, marker::PointeeSized};

#[extern_spec]
trait PartialEq<Rhs> {
    #[trusted]
    #[pure]
    // #[refine_spec(where Self: PureEq, [pure])]
    // #[refine_spec(where Self = Rhs, [ensures((*self === *other) ==> result)])]
    fn eq(&self, other: &Rhs) -> bool;

    #[trusted]
    #[pure]
    // #[refine_spec(where Self: PureEq, [pure])]
    #[ensures(result == !self.eq(other))]
    fn ne(&self, other: &Rhs) -> bool;
}

#[extern_spec]
impl PartialEq for () {
    #[trusted]
    #[pure]
    #[ensures(result)]
    fn eq(&self, _other: &()) -> bool;
}

/// Relates `PartialEq` on the primitive types to their built-in comparison.
/// Without this the impls are encoded as uninterpreted functions, which is
/// invisible for a direct `a == b` (that compiles to a `BinOp`) but blocks
/// any generic specification that reaches them, e.g. `PartialEq for
/// Option<T>` comparing its payloads at `T`.
///
/// The right hand side is the built-in comparison rather than snapshot
/// equality, so this also holds for the floats, where `NaN` is equal to
/// nothing, itself included.
macro_rules! impl_partial_eq_primitive {
    ($($ty:ty),*) => {$(
        #[extern_spec]
        impl PartialEq for $ty {
            #[trusted]
            #[pure]
            #[ensures(result == (*self == *other))]
            fn eq(&self, other: &$ty) -> bool;
        }
    )*};
}

impl_partial_eq_primitive!(
    bool, char, i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize, f32, f64
);

/// Relates `PartialEq` on the tuples to the comparison of their fields, which
/// is what the standard library implements them as. Built recursively like
/// `core`'s own `tuple_impls!`, so the invocation for the longest tuple also
/// covers every shorter one.
macro_rules! impl_partial_eq_tuple {
    // Stopping criteria (1-ary tuple)
    ($T:ident) => {
        impl_partial_eq_tuple!(@impl $T);
    };
    // Running criteria (n-ary tuple, with n >= 2)
    ($T:ident $( $U:ident )+) => {
        impl_partial_eq_tuple!($( $U )+);
        impl_partial_eq_tuple!(@impl $T $( $U )+);
    };
    // "Private" internal implementation
    (@impl $( $T:ident )+) => {
        #[extern_spec]
        impl<$($T: PartialEq),+> PartialEq for ($($T,)+) {
            #[trusted]
            #[pure]
            #[ensures(result == ($( ${ignore($T)} self.${index()} == other.${index()} )&&+))]
            fn eq(&self, other: &($($T,)+)) -> bool;
        }
    };
}

impl_partial_eq_tuple!(E D C B A Z Y X W V U T);

#[extern_spec]
impl<T: PartialEq> PartialEq for Option<T> {
    #[trusted]
    #[pure]
    #[ensures(result == match (self, other) {
        (Some(l), Some(r)) => *l == *r,
        (None, None) => true,
        _ => false,
    })]
    fn eq(&self, other: &Option<T>) -> bool;
}

macro_rules! impl_partial_eq_ref {
    ($lhs:ty, $rhs:ty) => {
        #[extern_spec]
        impl<A: PointeeSized, B: PointeeSized> PartialEq<$rhs> for $lhs
        where
            A: PartialEq<B>,
        {
            #[trusted]
            #[pure]
            #[ensures(result == PartialEq::eq(*self, *other))]
            fn eq(&self, other: &$rhs) -> bool;

            #[trusted]
            #[pure]
            #[ensures(result == PartialEq::ne(*self, *other))]
            fn ne(&self, other: &$rhs) -> bool;
        }
    };
}

impl_partial_eq_ref!(&A, &B);
// TODO: restore once `&mut` is supported in specifications. `*self` and
// `*other` relate the result to an unconstrained value rather than to the
// referents, and these are encoded for every program mentioning `PartialEq`.
// impl_partial_eq_ref!(&mut A, &mut B);
// impl_partial_eq_ref!(&A, &mut B);
// impl_partial_eq_ref!(&mut A, &B);

/// Specifies that `PartialEq::eq`, if implemented, is a pure method, allowing its usage in specs.
pub auto trait PureEq {}
