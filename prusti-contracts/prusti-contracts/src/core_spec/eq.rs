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
impl_partial_eq_ref!(&mut A, &mut B);
impl_partial_eq_ref!(&A, &mut B);
impl_partial_eq_ref!(&mut A, &B);

/// Specifies that `PartialEq::eq`, if implemented, is a pure method, allowing its usage in specs.
pub auto trait PureEq {}
