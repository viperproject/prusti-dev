use crate::*;

#[allow(unused_imports)]
use core::ops::{Deref, DerefMut};
#[allow(unused_imports)]
use core::option::*;
#[allow(unused_imports)]
use core::pin::Pin;

// NOTE: these are all non-nightly methods without trait bounds as of 2022-09

// FUTURE(unsupported_constants): reference None as a constant where it makes sense, rather than .is_none()
#[extern_spec]
impl<T> Option<T> {
    #[pure]
    #[ensures(result == matches!(self, Some(_)))]
    fn is_some(&self) -> bool;

    #[pure]
    #[ensures(result == matches!(self, None))]
    fn is_none(&self) -> bool;

    #[ensures(result.is_some() == self.is_some())]
    // FUTURE(refs): ensure identity matches
    //#[ensures(match self {
    //    Some(v) => *result.unwrap() == v,
    //    None => result.is_none(),
    //})]
    fn as_ref(&self) -> Option<&T>;

    #[ensures(result.is_some() == self.is_some())]
    // FUTURE(refs): ensure identity matches
    fn as_mut(&mut self) -> Option<&mut T>;

    #[ensures(result.is_some() == self.is_some())]
    // FUTURE(refs): ensure identity matches
    fn as_pin_ref(self: Pin<&Option<T>>) -> Option<Pin<&T>>;

    #[ensures(result.is_some() == self.is_some())]
    // FUTURE(refs): ensure identity matches
    fn as_pin_mut(self: Pin<&mut Option<T>>) -> Option<Pin<&mut T>>;

    #[requires(self.is_some())]
    #[ensures(old(self) === Some(result))]
    fn expect(self, msg: &str) -> T;

    #[requires(self.is_some())]
    #[ensures(old(self) === Some(result))]
    fn unwrap(self) -> T;

    #[ensures(match old(self) {
        Some(v) => result === v,
        None => result === default,
    })]
    fn unwrap_or(self, default: T) -> T;

    #[ensures(match old(self) {
        Some(v) => result === v,
        None => true,
    })]
    // FUTURE(calls): describe that the function is called if none
    fn unwrap_or_else<F>(self, f: F) -> T
    where
        F: FnOnce() -> T;

    #[ensures(old(self.is_none()) || old(self) === Some(result))]
    #[refine_spec(where T: super::default::PureDefault, [
        ensures(result === match old(self) {
            Some(v) => v,
            None => Default::default(),
        })
    ])]
    // FUTURE(calls): describe as call to Default::default rather than PureDefault
    fn unwrap_or_default(self) -> T
    where
        T: Default;

    #[requires(self.is_some())]
    #[ensures(old(self) === Some(result))]
    unsafe fn unwrap_unchecked(self) -> T;

    #[ensures(result.is_some() == old(self.is_some()))]
    // FUTURE(calls): describe that and how the function is called if some, and that its result is returned
    fn map<U, F>(self, f: F) -> Option<U>
    where
        F: FnOnce(T) -> U;

    #[ensures(old(self.is_none()) ==> result === default)]
    // FUTURE(calls): describe that and how the function is called if some, and that its result is returned
    fn map_or<U, F>(self, default: U, f: F) -> U
    where
        F: FnOnce(T) -> U;

    // FUTURE(calls): describe all function calls involved here and how they affect the result
    fn map_or_else<U, D, F>(self, default: D, f: F) -> U
    where
        D: FnOnce() -> U,
        F: FnOnce(T) -> U;

    #[ensures(result === match old(self) {
        Some(v) => Ok(v),
        None => Err(err),
    })]
    fn ok_or<E>(self, err: E) -> Result<T, E>;

    #[ensures(match old(self) {
        Some(v) => result === Ok(v),
        None => result.is_err(),
    })]
    // FUTURE(calls): describe call to error function if none, and that its result is returned
    fn ok_or_else<E, F>(self, err: F) -> Result<T, E>
    where
        F: FnOnce() -> E;

    #[ensures(self.is_some() == result.is_some())]
    // FUTURE(refs): describe using PureDeref or call description if available
    // FUTURE(calls): describe as call to Deref::deref if some
    fn as_deref(&self) -> Option<&<T as Deref>::Target>
    where
        T: Deref;

    #[ensures(self.is_some() == result.is_some())]
    // FUTURE(calls): describe as call to DerefMut::deref_mut if some
    fn as_deref_mut(&mut self) -> Option<&mut <T as Deref>::Target>
    where
        T: DerefMut;

    // FUTURE(iterators): describe what the iterator will yield
    fn iter(&self) -> Iter<'_, T>;

    // FUTURE(iterators): describe what the iterator will yield
    fn iter_mut(&mut self) -> IterMut<'_, T>;

    #[ensures(match old(self) {
        Some(_) => result === old(optb),
        None => result.is_none(),
    })]
    fn and<U>(self, optb: Option<U>) -> Option<U>;

    #[ensures(old(self.is_none()) ==> result.is_none())]
    // FUTURE(calls): describe call to function if some, and that its result is returned
    fn and_then<U, F>(self, f: F) -> Option<U>
    where
        F: FnOnce(T) -> Option<U>;

    #[ensures(match old(self) {
        Some(v) => result.is_none() || result === Some(v),
        None => result.is_none(),
    })]
    // FUTURE(calls): describe call to function if some, and how it affects result
    fn filter<P>(self, predicate: P) -> Option<T>
    where
        P: FnOnce(&T) -> bool;

    #[ensures(result === match old(self) {
        Some(v) => Some(v),
        None => old(optb),
    })]
    fn or(self, optb: Option<T>) -> Option<T>;

    #[ensures(old(self.is_some()) ==> result.is_some())]
    // FUTURE(calls): describe call to function if none, and that its result is returned
    fn or_else<F>(self, f: F) -> Option<T>
    where
        F: FnOnce() -> Option<T>;

    #[ensures(result === match (old(self), old(optb)) {
        (Some(v0), None) => Some(v0),
        (None, Some(v0)) => Some(v0),
        _ => None,
    })]
    fn xor(self, optb: Option<T>) -> Option<T>;

    #[ensures(*result === value)]
    #[after_expiry(snap(self) === Some(before_expiry(snap(result))))]
    fn insert(&mut self, value: T) -> &mut T;

    #[ensures(match old(self) {
        Some(v) => *result === v,
        None => *result === value,
    })]
    #[after_expiry(snap(self) === Some(before_expiry(snap(result))))]
    fn get_or_insert(&mut self, value: T) -> &mut T;

    #[ensures(match old(self) {
        Some(v) => *result === v,
        None => true,
    })]
    #[after_expiry(snap(self) === Some(before_expiry(snap(result))))]
    // FUTURE(calls): describe call to function if none, and that its result is returned and placed in the option
    fn get_or_insert_with<F>(&mut self, f: F) -> &mut T
    where
        F: FnOnce() -> T;

    #[ensures(result === old(snap(self)))]
    #[ensures(self.is_none())]
    fn take(&mut self) -> Option<T>;

    #[ensures(result === old(snap(self)))]
    #[ensures(*self === Some(value))]
    fn replace(&mut self, value: T) -> Option<T>;

    #[ensures(match (old(self), old(other)) {
        (Some(v0), Some(v1)) => result === Some((v0, v1)),
        _ => result.is_none(),
    })]
    fn zip<U>(self, other: Option<U>) -> Option<(T, U)>;

    // TODO: specific methods depending on trait bounds? flatten especially might be useful
}
