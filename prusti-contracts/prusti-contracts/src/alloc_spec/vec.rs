use crate::*;
use std::{alloc::Allocator, slice::SliceIndex, vec::Vec};

#[extern_spec]
impl<T> Vec<T> {
    #[trusted]
    #[ensures(result.is_empty())]
    fn new() -> Self;

    #[trusted]
    // capacity is not relevant to functional behavior
    #[ensures(result.is_empty())]
    fn with_capacity(capacity: usize) -> Self;
}

#[extern_spec]
impl<T, A: core::alloc::Allocator> Vec<T, A> {
    #[trusted]
    #[pure]
    #[ensures(result == (self.len() == 0))]
    #[ensures(result == self.as_slice().is_empty())]
    fn is_empty(&self) -> bool;

    #[trusted]
    #[pure]
    #[ensures(result == self.as_slice().len())]
    fn len(&self) -> usize;

    #[trusted]
    #[pure]
    #[ensures(result.len() == self.len())]
    fn as_slice(&self) -> &[T];

    #[trusted]
    #[ensures(self.is_empty())]
    fn clear(&mut self);

    #[trusted]
    #[ensures(self.len() == old(self.len()) + 1)]
    #[ensures(self[self.len() - 1] === value)]
    #[ensures(forall(|i: usize| i < old(self.len()) ==> &self[i] === old(&self[i])))]
    fn push(&mut self, value: T);
}

#[extern_spec]
impl<T, I, A> core::ops::Index<I> for Vec<T, A>
where
    I: SliceIndex<[T]>,
    A: Allocator,
{
    #[trusted]
    #[pure]
    fn index(&self, index: I) -> &I::Output;
}

#[extern_spec]
impl<T, I, A> core::ops::IndexMut<I> for Vec<T, A>
where
    I: SliceIndex<[T]>,
    A: Allocator,
{
    #[trusted]
    #[ensures(*result === *old(&self[index]))]
    #[after_expiry(self[index] === *before_expiry(&*result))]
    fn index_mut(&mut self, index: I) -> &mut I::Output;
}
