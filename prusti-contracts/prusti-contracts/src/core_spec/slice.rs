use crate::*;

use core::slice::SliceIndex;

#[extern_spec]
impl<T> [T] {
    #[trusted]
    #[pure]
    #[ensures(result == core::intrinsics::ptr_metadata(self))]
    fn len(&self) -> usize;
}

#[extern_spec]
pub unsafe trait SliceIndex<T>
where
    T: ?Sized,
{
    #[trusted]
    #[pure]
    fn index(self, slice: &T) -> &Self::Output;
}

#[extern_spec]
impl<T, I> core::ops::Index<I> for [T]
where
    I: SliceIndex<[T]>,
{
    #[trusted]
    #[pure]
    #[ensures(result === SliceIndex::index(index, self))]
    fn index(&self, index: I) -> &I::Output;
}
