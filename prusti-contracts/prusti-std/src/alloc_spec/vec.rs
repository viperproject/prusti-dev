use prusti_contracts::*;

use alloc::{alloc::Allocator, vec::Vec};

#[extern_spec]
impl<T> Vec<T> {
    #[ensures(result.is_empty())]
    fn new() -> Self;
}

// FUTURE(#1221): Vec should forward its specs to as_slice where possible, to avoid writing each spec twice.
// That doesn't currently work though, due to issue #1221
#[extern_spec]
impl<T, A: Allocator> Vec<T, A> {
    #[pure]
    #[ensures(result == (self.len() == 0))]
    //#[ensures(result == self.as_slice().is_empty())]
    fn is_empty(&self) -> bool;

    #[pure]
    //#[ensures(result == self.as_slice().len())]
    fn len(&self) -> usize;

    #[pure]
    #[ensures(result.len() == self.len())]
    fn as_slice(&self) -> &[T];

    #[ensures(self.is_empty())]
    fn clear(&mut self);

    #[ensures(self.len() == old(self.len()) + 1)]
    //#[ensures(self[self.len() - 1] === value)]
    //#[ensures(forall(|i: usize| i < old(self.len()) ==> &self[i] === old(&self[i])))]
    fn push(&mut self, value: T);
}

// FUTURE(#1221): We'd like to specify the behavior of Index for Vec, but issue #1221 is currently blocking that. Once it's fixed, Prusti can be amended to rely on these specs instead of rejecting the index operation because Vec doesn't have hardcoded support.
/*
use core::{ops::Index, slice::SliceIndex};

#[extern_spec]
impl<T, A: Allocator, I: SliceIndex<[T]>> Index<I> for Vec<T, A> {
    #[pure]
    #[ensures(*result === self.as_slice()[index])]
    fn index(&self, index: I) -> &Self::Output;
}
*/

#[extern_spec]
impl<T> Default for Vec<T> {
    #[refine_spec(where Self: Copy, [pure])]
    #[ensures(result.is_empty())]
    fn default() -> Self;
}
