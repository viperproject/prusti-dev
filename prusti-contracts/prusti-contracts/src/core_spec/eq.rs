use crate::*;

use core::cmp::PartialEq;

#[extern_spec]
trait PartialEq<Rhs> {
    #[pure]
    // #[refine_spec(where Self: PureEq, [pure])]
    // #[refine_spec(where Self = Rhs, [ensures((*self === *other) ==> result)])]
    fn eq(&self, other: &Rhs) -> bool;

    #[pure]
    // #[refine_spec(where Self: PureEq, [pure])]
    #[ensures(result == !self.eq(other))]
    fn ne(&self, other: &Rhs) -> bool;
}

/// Specifies that `PartialEq::eq`, if implemented, is a pure method, allowing its usage in specs.
pub auto trait PureEq {}
