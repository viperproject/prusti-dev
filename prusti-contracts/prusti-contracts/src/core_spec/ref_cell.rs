//! `RefCell` and its guards.
//!
//! The model follows the implementation. A `RefCell` owns a borrow counter
//! (a `Cell<isize>`: `0` = free, `n > 0` = `n` shared borrows, `-1` =
//! mutably borrowed) and the value. A guard holds a shared reference to the
//! same counter cell and a raw pointer to the same value. The permission to
//! the value is split by counting: each `Ref` holds `1 / isize::MAX` of it, a
//! `RefMut` all of it, and the `RefCell` whatever the counter says is left.
//! The shares of one value are fractions of one object, so nothing has to be
//! handed back when a guard dies: dropping a guard updates the counter (see
//! the `Drop` contracts), which by itself grows the `RefCell`'s share.

use super::im_deref;
use crate::*;

use core::{
    cell::{BorrowError, BorrowMutError, Cell, Ref, RefCell, RefMut},
    ops::{Deref, DerefMut},
};

/// The share of the value a `RefCell` holds itself under borrow count `n`.
#[pure]
#[ensures(n == 0 ==> result == Real::WRITE)]
#[ensures(0 < n && n < isize::MAX ==> Real::NONE < result && result < Real::WRITE)]
pub fn refcell_share(n: isize) -> Real {
    match n {
        n if n >= 0 => (Real::from(isize::MAX) - Real::from(n)) / Real::from(isize::MAX),
        _ => Real::NONE,
    }
}

/// The share of the value each `Ref` guard holds.
#[pure]
#[ensures(Real::NONE < result && result < Real::WRITE)]
pub fn ref_share() -> Real {
    Real::WRITE / Real::from(isize::MAX)
}

/// The borrow counter of a `RefCell`.
#[pure]
#[trusted]
#[field_projection(borrow)]
pub fn refcell_flag<T: ?Sized>(_c: &RefCell<T>) -> &Cell<isize> {
    unimplemented!()
}

/// The borrow counter a `Ref` guard points to.
#[pure]
#[trusted]
#[field_projection(borrow.borrow)]
pub fn ref_flag<'b, T: ?Sized + 'b>(_r: &Ref<'b, T>) -> &'b Cell<isize> {
    unimplemented!()
}

/// The borrow counter a `RefMut` guard points to.
#[pure]
#[trusted]
#[field_projection(borrow.borrow)]
pub fn refmut_flag<'b, T: ?Sized + 'b>(_r: &RefMut<'b, T>) -> &'b Cell<isize> {
    unimplemented!()
}

/// The value a `Ref` guard points to, of which it holds [`ref_share`].
#[pure]
#[interior_mut(ref_share())]
#[trusted]
#[field_projection(value.pointer)]
pub fn ref_value_ptr<'b, T: ?Sized + 'b>(_r: &Ref<'b, T>) -> *const T {
    unimplemented!()
}

/// The value a `RefMut` guard points to, all of which it holds.
#[pure]
#[interior_mut]
#[trusted]
#[field_projection(value.pointer)]
pub fn refmut_value_ptr<'b, T: ?Sized + 'b>(_r: &RefMut<'b, T>) -> *const T {
    unimplemented!()
}

/// The number of outstanding dynamic borrows of a `RefCell`: `0` = free,
/// `n > 0` = `n` shared borrows, `-1` = mutably borrowed.
#[pure_unstable(true)]
pub fn refcell_count<T: ?Sized>(c: &RefCell<T>) -> isize {
    refcell_flag(c).get()
}

/// The borrow count as seen through a `Ref` guard.
#[pure_unstable(true)]
pub fn ref_count<'b, T: ?Sized + 'b>(r: &Ref<'b, T>) -> isize {
    ref_flag(r).get()
}

/// The borrow count as seen through a `RefMut` guard.
#[pure_unstable(true)]
pub fn refmut_count<'b, T: ?Sized + 'b>(r: &RefMut<'b, T>) -> isize {
    refmut_flag(r).get()
}

/// A reference to the current value of a `RefCell` (readable while the
/// `RefCell` holds a share of it, i.e. unless it is mutably borrowed).
#[pure_unstable]
pub fn refcell_value<T: ?Sized>(c: &RefCell<T>) -> &T {
    im_deref(c.as_ptr())
}

/// The value a `Ref` guard dereferences to.
#[pure_unstable(true)]
pub fn ref_value<'a, 'b, T: ?Sized + 'b>(r: &'a Ref<'b, T>) -> &'a T {
    im_deref(ref_value_ptr(r))
}

/// The value a `RefMut` guard dereferences to.
#[pure_unstable(true)]
pub fn refmut_value<'a, 'b, T: ?Sized + 'b>(r: &'a RefMut<'b, T>) -> &'a T {
    im_deref(refmut_value_ptr(r))
}

#[extern_spec]
impl<T: ?Sized> RefCell<T> {
    #[pure_unstable(true)]
    #[interior_mut(refcell_share(refcell_count(self)))]
    #[trusted]
    pub fn as_ptr(&self) -> *mut T;

    #[trusted]
    #[requires(0 <= refcell_count(self) && refcell_count(self) < isize::MAX)]
    #[ensures(refcell_count(self) == old(refcell_count(self)) + 1)]
    // The guard aliases the cell's counter and value.
    #[ensures(ref_flag(&result).as_ptr() === refcell_flag(self).as_ptr())]
    #[ensures(ref_value_ptr(&result) === self.as_ptr() as *const T)]
    #[ensures(*refcell_value(self) === *old(refcell_value(self)))]
    pub fn borrow(&self) -> Ref<'_, T>;

    #[trusted]
    #[requires(refcell_count(self) == 0)]
    #[ensures(refcell_count(self) == -1)]
    #[ensures(refmut_flag(&result).as_ptr() === refcell_flag(self).as_ptr())]
    #[ensures(refmut_value_ptr(&result) === self.as_ptr() as *const T)]
    #[ensures(*refmut_value(&result) === *old(refcell_value(self)))]
    pub fn borrow_mut(&self) -> RefMut<'_, T>;

    #[trusted]
    #[ensures(match &result {
        Ok(g) => 0 <= old(refcell_count(self))
            && old(refcell_count(self)) < isize::MAX
            && refcell_count(self) == old(refcell_count(self)) + 1
            && ref_flag(g).as_ptr() === refcell_flag(self).as_ptr()
            && ref_value_ptr(g) === self.as_ptr() as *const T
            && *refcell_value(self) === *old(refcell_value(self)),
        Err(_) => !(0 <= old(refcell_count(self)) && old(refcell_count(self)) < isize::MAX)
            && refcell_count(self) == old(refcell_count(self)),
    })]
    pub fn try_borrow(&self) -> Result<Ref<'_, T>, BorrowError>;

    #[trusted]
    #[ensures(match &result {
        Ok(g) => old(refcell_count(self)) == 0
            && refcell_count(self) == -1
            && refmut_flag(g).as_ptr() === refcell_flag(self).as_ptr()
            && refmut_value_ptr(g) === self.as_ptr() as *const T
            && *refmut_value(g) === *old(refcell_value(self)),
        Err(_) => old(refcell_count(self)) != 0
            && refcell_count(self) == old(refcell_count(self)),
    })]
    pub fn try_borrow_mut(&self) -> Result<RefMut<'_, T>, BorrowMutError>;

    #[trusted]
    // `&mut self` statically excludes live guards, but a leaked guard can
    // leave the count permanently nonzero, so the free state is a
    // precondition rather than a given.
    #[requires(refcell_count(&*self) == 0)]
    #[ensures(*result === *old(refcell_value(&*self)))]
    #[after_expiry(refcell_count(&*self) == 0
        && Ghost::new_ref(refcell_value(&*self))
            == before_expiry(Ghost::new_ref(&*result)))]
    pub fn get_mut(&mut self) -> &mut T;
}

// Dropping a guard leaves its own fields (the value pointer and the reference
// to the borrow flag) as they were: only the flag's content changes.
#[extern_spec]
impl<T: ?Sized> Drop for Ref<'_, T> {
    #[ensures(*self === *old(&*self))]
    #[ensures(ref_count(self) == old(ref_count(self)) - 1)]
    #[ensures(*ref_value(self) === *old(ref_value(self)))]
    fn drop(&mut self);
}

#[extern_spec]
impl<T: ?Sized> Drop for RefMut<'_, T> {
    #[ensures(*self === *old(&*self))]
    #[ensures(refmut_count(self) == old(refmut_count(self)) + 1)]
    #[ensures(*refmut_value(self) === *old(refmut_value(self)))]
    fn drop(&mut self);
}

// The guards' `deref` reads interior-mutable state, so it is a
// `#[pure_unstable]` function: the state it reads is then an ordinary
// argument. (As a postcondition of an impure trait method it would end up in
// a trait-impl axiom, where heap-dependent reads are impossible.)
#[extern_spec]
impl<T: ?Sized> Deref for Ref<'_, T> {
    #[pure_unstable(true)]
    #[trusted]
    #[ensures(result === ref_value(self))]
    fn deref<'a>(&'a self) -> &'a T;
}

#[extern_spec]
impl<T: ?Sized> Deref for RefMut<'_, T> {
    #[pure_unstable(true)]
    #[trusted]
    #[ensures(result === refmut_value(self))]
    fn deref<'a>(&'a self) -> &'a T;
}

#[extern_spec]
impl<T: ?Sized> DerefMut for RefMut<'_, T> {
    #[trusted]
    #[ensures(*result === *old(refmut_value(&*self)))]
    // The guard itself (its value pointer and flag reference) is untouched
    // by the borrow of the value: only what it points to changes.
    #[after_expiry(*self === *old(&*self)
        && Ghost::new_ref(refmut_value(&*self)) == before_expiry(Ghost::new_ref(&*result)))]
    fn deref_mut<'a>(&'a mut self) -> &'a mut T;
}

#[extern_spec]
impl<T> RefCell<T> {
    #[trusted]
    #[ensures(*refcell_value(&result) === value)]
    #[ensures(refcell_count(&result) == 0)]
    pub fn new(value: T) -> RefCell<T>;

    #[trusted]
    #[requires(refcell_count(self) == 0)]
    #[ensures(refcell_count(self) == 0)]
    #[ensures(result === *old(refcell_value(self)))]
    #[ensures(*refcell_value(self) === val)]
    pub fn replace(&self, val: T) -> T;

    #[trusted]
    #[requires(refcell_count(self) == 0 && refcell_count(other) == 0)]
    #[ensures(refcell_count(self) == 0 && refcell_count(other) == 0)]
    /// Also correct when `self` and `other` alias: the old values are then
    /// equal, so exchanging them is a no-op.
    #[ensures(*refcell_value(self) === *old(refcell_value(other)))]
    #[ensures(*refcell_value(other) === *old(refcell_value(self)))]
    pub fn swap(&self, other: &RefCell<T>);

    #[trusted]
    #[ensures(result === *old(refcell_value(&self)))]
    pub fn into_inner(self) -> T;
}

#[extern_spec]
impl<T: Default> RefCell<T> {
    #[trusted]
    #[requires(refcell_count(self) == 0)]
    #[ensures(refcell_count(self) == 0)]
    #[ensures(result === *old(refcell_value(self)))]
    #[ensures(*refcell_value(self) === T::default())]
    pub fn take(&self) -> T;
}

// TODO: `impl Default for RefCell<T>` cannot be usefully specced yet: the
// blanket trait-level `#[pure]` on `Default::default` (needed so specs like
// `take`'s can call `T::default()`) makes `RefCell::default()` a pure
// constructor, which mints no interior-mutability permissions. Requires
// conditional purity (`refine_spec(where Self: PureDefault, [pure])`).
//
// TODO: `impl<T> From<T> for RefCell<T>` hits a missing generic-to-concrete
// cast in the trait-impl spec encoding (the trait fn's `Self`-typed result
// is bound as `s_Param` where the impl spec expects the concrete snapshot),
// producing a Viper consistency error. Spec it once that cast is fixed.
