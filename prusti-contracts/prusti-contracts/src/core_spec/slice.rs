use crate::*;

#[allow(unused_imports)]
use core::{ops::Index, slice::SliceIndex};

#[extern_spec]
impl<T> [T] {
    #[pure]
    #[ensures(result == (self.len() == 0))]
    fn is_empty(&self) -> bool;

    #[pure]
    fn len(&self) -> usize;

    #[ensures(match result {
        Some(x) => *x === self[0],
        None => self.len() == 0,
    })]
    // FUTURE(refs): make statements about the returned reference
    fn first(&self) -> Option<&T>;

    #[ensures(match result {
        Some(x) => *x === self[0],
        None => self.len() == 0,
    })]
    // FUTURE(refs): make statements about the returned reference
    fn first_mut(&mut self) -> Option<&mut T>;

    #[ensures(match result {
        Some(x) => *x === self[self.len() - 1],
        None => self.len() == 0,
    })]
    // FUTURE(refs): make statements about the returned reference
    fn last(&self) -> Option<&T>;

    #[ensures(match result {
        Some(x) => *x === self[self.len() - 1],
        None => self.len() == 0,
    })]
    // FUTURE(refs): make statements about the returned reference
    fn last_mut(&mut self) -> Option<&mut T>;
}

// FUTURE(#1221): This spec is currently not usable due to issue #1221.
#[extern_spec]
impl<T, I> Index<I> for [T]
where
    I: SliceIndex<[T]>,
{
    #[pure]
    fn index(&self, index: I) -> &I::Output;
}
