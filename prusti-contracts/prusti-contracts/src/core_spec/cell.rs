use crate::*;

use core::cell::Cell;

#[extern_spec]
impl<T> Cell<T> {
    #[pure]
    #[interior_mut]
    pub fn as_ptr(&self) -> *mut T;
}

#[extern_spec]
impl<T: Copy> Cell<T> {
    /// The current value of the cell. Reads interior-mutable state, so it is
    /// `pure_unstable`: its value depends on the inner-IM-QP snapshot.
    #[trusted]
    #[pure_unstable(true)]
    pub fn get(&self) -> T;

    #[ensures(result.get() === value)]
    pub fn new(value: T) -> Cell<T>;

    #[ensures(self.get() === val)]
    pub fn set(&self, val: T);

    #[ensures(result === old(self.get()))]
    #[ensures(self.get() === val)]
    pub fn replace(&self, val: T) -> T;

    /// Also correct when `self` and `other` alias: the old values are then
    /// equal, so exchanging them is a no-op.
    #[ensures(self.get() === old(other.get()))]
    #[ensures(other.get() === old(self.get()))]
    pub fn swap(&self, other: &Cell<T>);

    #[ensures(result === old(self.get()))]
    pub fn into_inner(self) -> T;

    // TODO: also relate the value after the borrow expires:
    // `#[after_expiry(self.get() === before_expiry(*result))]`.
    #[ensures(*result === old(self.get()))]
    pub fn get_mut(&mut self) -> &mut T;

    // TODO: also relate the value after the borrow expires:
    // `#[after_expiry(*t === before_expiry(result.get()))]`.
    #[ensures(result.get() === old(*t))]
    pub fn from_mut(t: &mut T) -> &Cell<T>;
}

#[extern_spec]
impl<T: Copy + Default> Cell<T> {
    #[ensures(result === old(self.get()))]
    #[ensures(self.get() === T::default())]
    pub fn take(&self) -> T;
}
