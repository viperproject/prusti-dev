use crate::*;

use core::slice::SliceIndex;

#[extern_spec]
impl<T> [T] {
    #[trusted]
    #[pure]
    #[ensures(result == core::intrinsics::ptr_metadata(self))]
    fn len(&self) -> usize;

    #[trusted]
    #[pure]
    #[ensures(result == (self.len() == 0))]
    fn is_empty(&self) -> bool;
}

/// Whether the slice index `index` addresses position `pos`. Uninterpreted;
/// the spec of each `SliceIndex` impl defines it for its own index type
/// (as postconditions of `SliceIndex::index`), so generic specs (e.g. of
/// `IndexMut`) can frame the positions an index does not touch.
#[pure]
#[trusted]
pub fn slice_index_touches<I>(_index: &I, _pos: usize) -> bool {
    unimplemented!()
}

#[extern_spec]
impl<T> SliceIndex<[T]> for usize {
    #[trusted]
    #[pure]
    // TODO: Convert to quantifier once custom triggers are supported
    #[ensures(slice_index_touches(&self, 0) == (self == 0))]
    #[ensures(slice_index_touches(&self, 1) == (self == 1))]
    #[ensures(slice_index_touches(&self, 2) == (self == 2))]
    fn index(self, slice: &[T]) -> &T;
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
