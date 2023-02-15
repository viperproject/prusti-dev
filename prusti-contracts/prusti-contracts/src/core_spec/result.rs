use crate::*;

#[allow(unused_imports)]
use core::fmt::Debug;
#[allow(unused_imports)]
use core::ops::{Deref, DerefMut};
#[allow(unused_imports)]
use core::result::*;

#[extern_spec]
impl<T, E> Result<T, E> {
    #[pure]
    #[ensures(result == matches!(self, Ok(_)))]
    fn is_ok(&self) -> bool;

    #[pure]
    #[ensures(result == matches!(self, Err(_)))]
    fn is_err(&self) -> bool;

    #[ensures(result === match old(self) {
        Ok(v) => Some(v),
        Err(_) => None,
    })]
    fn ok(self) -> Option<T>;

    #[ensures(result === match old(self) {
        Ok(_) => None,
        Err(e) => Some(e),
    })]
    fn err(self) -> Option<E>;

    #[ensures(result.is_ok() == self.is_ok())]
    // FUTURE(refs): ensure identity matches
    fn as_ref(&self) -> Result<&T, &E>;

    #[ensures(result.is_ok() == old(self.is_ok()))]
    // FUTURE(refs): ensure identity matches & result affects original
    fn as_mut(&mut self) -> Result<&mut T, &mut E>;

    #[ensures(result.is_ok() == old(self.is_ok()))]
    // FUTURE(calls): describe that and how the function is called if ok, and that its result is returned
    fn map<U, F>(self, op: F) -> Result<U, E>
    where
        F: FnOnce(T) -> U;

    #[ensures(old(self.is_err()) ==> result === default)]
    // FUTURE(calls): describe that and how the function is called if ok, and that its result is returned
    fn map_or<U, F>(self, default: U, op: F) -> U
    where
        F: FnOnce(T) -> U;

    // FUTURE(calls): describe all function calls involved here and how they affect the result
    fn map_or_else<U, D, F>(self, default: D, f: F) -> U
    where
        D: FnOnce(E) -> U,
        F: FnOnce(T) -> U;

    #[ensures(match old(self) {
        Ok(v) => result === Ok(v),
        Err(_) => result.is_err(),
    })]
    // FUTURE(calls): describe that and how the function is called if err, and that its result is returned
    fn map_err<F, O>(self, op: O) -> Result<T, F>
    where
        O: FnOnce(E) -> F;

    #[ensures(match self {
        Ok(v) => result.is_ok(),
        Err(e) => result === Err(e),
    })]
    // FUTURE(calls): describe as call to Deref::deref if some
    // FUTURE(refs): describe transformation of ok value and error not changing
    fn as_deref(&self) -> Result<&<T as Deref>::Target, &E>
    where
        T: Deref;

    #[ensures(result.is_ok() == old(self.is_ok()))]
    // FUTURE(calls): describe as call to Deref::deref if some
    // FUTURE(refs): describe transformation of ok value and error not changing
    fn as_deref_mut(&mut self) -> Result<&mut <T as Deref>::Target, &mut E>
    where
        T: DerefMut;

    // FUTURE(iterators): describe what the iterator will yield
    fn iter(&self) -> Iter<'_, T>;

    // FUTURE(iterators): describe what the iterator will yield
    fn iter_mut(&mut self) -> IterMut<'_, T>;

    #[requires(self.is_ok())]
    #[ensures(old(self) === Ok(result))]
    fn expect(self, msg: &str) -> T
    where
        E: Debug;

    #[requires(self.is_ok())]
    #[ensures(old(self) === Ok(result))]
    fn unwrap(self) -> T
    where
        E: Debug;

    #[ensures(old(self.is_err()) || old(self) === Ok(result))]
    #[refine_spec(where T: Copy + super::default::PureDefault, [
        ensures(result === match old(self) {
            Ok(v) => v,
            Err(_) => T::default(),
        })
    ])]
    // FUTURE(calls): describe as call to Default::default if err
    fn unwrap_or_default(self) -> T
    where
        T: Default;

    #[requires(self.is_err())]
    #[ensures(old(self) === Err(result))]
    fn expect_err(self, msg: &str) -> E
    where
        T: Debug;

    #[requires(self.is_err())]
    #[ensures(old(self) === Err(result))]
    fn unwrap_err(self) -> E
    where
        T: Debug;

    #[ensures(result === match old(self) {
        Ok(v) => old(res),
        Err(e) => Err(e),
    })]
    fn and<U>(self, res: Result<U, E>) -> Result<U, E>;

    #[ensures(match old(self) {
        Ok(v) => true,
        Err(e) => result === Err(e),
    })]
    // FUTURE(calls): describe call to function if ok, and that its result is returned
    fn and_then<U, F>(self, f: F) -> Result<U, E>
    where
        F: FnOnce(T) -> Result<U, E>;

    #[ensures(result === match old(self) {
        Ok(v) => Ok(v),
        Err(_) => old(res),
    })]
    fn or<F>(self, res: Result<T, F>) -> Result<T, F>;

    #[ensures(match old(self) {
        Ok(v) => result === Ok(v),
        Err(_) => true,
    })]
    // FUTURE(calls): describe call to function if err, and that its result is returned
    fn or_else<F, O>(self, op: O) -> Result<T, F>
    where
        O: FnOnce(E) -> Result<T, F>;

    #[ensures(result === match old(self) {
        Ok(v) => v,
        Err(_) => default,
    })]
    fn unwrap_or(self, default: T) -> T;

    #[ensures(match old(self) {
        Ok(v) => result === v,
        Err(_) => true,
    })]
    // FUTURE(calls): describe that the function is called if err
    fn unwrap_or_else<F>(self, op: F) -> T
    where
        F: FnOnce(E) -> T;

    #[requires(self.is_ok())]
    #[ensures(old(self) === Ok(result))]
    unsafe fn unwrap_unchecked(self) -> T;

    #[requires(self.is_err())]
    #[ensures(old(self) === Err(result))]
    unsafe fn unwrap_err_unchecked(self) -> E;

    // TODO: specific methods depending on trait bounds
}

#[extern_spec]
impl<T, E> Result<Option<T>, E> {
    #[ensures(match old(self) {
        Ok(Some(x)) => result === Some(Ok(x)),
        Ok(None) => result.is_none(),
        Err(e) => result === Some(Err(e)),
    })]
    pub fn transpose(self) -> Option<Result<T, E>>;
}
