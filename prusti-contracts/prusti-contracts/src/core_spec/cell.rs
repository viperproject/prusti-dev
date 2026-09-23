use crate::*;

use core::cell::Cell;

/// A reference to the current value of a `Cell`. Reads interior-mutable
/// state, so it is `pure_unstable`. Unlike `Cell::get` it requires neither
/// `T: Copy` nor `T: Sized`, so it can express the value specs of every
/// `Cell` method (whose extern specs may not assume bounds the target lacks).
#[pure_unstable(true)]
pub fn cell_value<T: ?Sized>(c: &Cell<T>) -> &T {
    super::im_deref(c.as_ptr())
}

#[extern_spec]
impl<T: ?Sized> Cell<T> {
    #[trusted]
    #[pure]
    #[interior_mut]
    pub fn as_ptr(&self) -> *mut T;

    #[trusted]
    #[ensures(*result === *old(cell_value(self)))]
    #[after_expiry(Ghost::new_ref(cell_value(&*self)) == before_expiry(Ghost::new_ref(&*result)))]
    pub fn get_mut(&mut self) -> &mut T;

    #[trusted]
    // The old value is captured as a `Ghost` *inside* `old` (rather than
    // `*old(t)`): the deref through the `&mut` must read in the old state,
    // where `t`'s referent is still accessible (in the post state its
    // permission is blocked behind the reborrow wand). `old(*t)` itself is
    // not writable for `T: ?Sized` (it would need a by-value temporary).
    #[ensures(Ghost::new_ref(cell_value(result)) == old(Ghost::new_ref(&*t)))]
    #[after_expiry(Ghost::new_ref(&*t) == before_expiry(Ghost::new_ref(cell_value(result))))]
    pub fn from_mut(t: &mut T) -> &Cell<T>;
}

#[extern_spec]
impl<T> Cell<T> {
    #[trusted]
    #[ensures(*cell_value(&result) === value)]
    pub fn new(value: T) -> Cell<T>;

    #[trusted]
    #[ensures(*cell_value(self) === val)]
    pub fn set(&self, val: T);

    #[trusted]
    #[ensures(result === *old(cell_value(self)))]
    #[ensures(*cell_value(self) === val)]
    pub fn replace(&self, val: T) -> T;

    #[trusted]
    /// Also correct when `self` and `other` alias: the old values are then
    /// equal, so exchanging them is a no-op.
    #[ensures(*cell_value(self) === *old(cell_value(other)))]
    #[ensures(*cell_value(other) === *old(cell_value(self)))]
    pub fn swap(&self, other: &Cell<T>);

    #[trusted]
    #[ensures(result === *old(cell_value(&self)))]
    pub fn into_inner(self) -> T;
}

#[extern_spec]
impl<T: Copy> Cell<T> {
    #[trusted]
    #[pure_unstable(true)]
    #[ensures(result === *cell_value(self))]
    pub fn get(&self) -> T;
}

#[extern_spec]
impl<T: Default> Cell<T> {
    #[trusted]
    #[ensures(result === *old(cell_value(self)))]
    #[ensures(*cell_value(self) === T::default())]
    pub fn take(&self) -> T;
}
