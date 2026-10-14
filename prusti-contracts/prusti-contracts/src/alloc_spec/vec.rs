use crate::{core_spec::slice::slice_index_touches, *};
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
    // TODO: Convert to quantifier once custom triggers are supported
    #[ensures(0 < old(self.len()) ==> &self[0] === old(&self[0]))]
    #[ensures(1 < old(self.len()) ==> &self[1] === old(&self[1]))]
    #[ensures(2 < old(self.len()) ==> &self[2] === old(&self[2]))]
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
    #[ensures(result === SliceIndex::index(index, self.as_slice()))]
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
    #[after_expiry(self.len() == old(self.len()))]
    // TODO: Convert to quantifier once custom triggers are supported
    #[after_expiry(0 < self.len() && !slice_index_touches(&index, 0) ==> &self[0] === old(&self[0]))]
    #[after_expiry(1 < self.len() && !slice_index_touches(&index, 1) ==> &self[1] === old(&self[1]))]
    #[after_expiry(2 < self.len() && !slice_index_touches(&index, 2) ==> &self[2] === old(&self[2]))]
    fn index_mut(&mut self, index: I) -> &mut I::Output;
}
