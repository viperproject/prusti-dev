use crate::*;

use core::{
    ops::{Range, RangeFrom, RangeFull, RangeInclusive, RangeTo, RangeToInclusive},
    slice::SliceIndex,
};

#[extern_spec]
impl<T> SliceIndex<[T]> for Range<usize> {
    #[trusted]
    #[pure]
    #[ensures(result.len() == self.end - self.start)]
    fn index(self, slice: &[T]) -> &[T];
}

#[extern_spec]
impl<T> SliceIndex<[T]> for RangeFrom<usize> {
    #[trusted]
    #[pure]
    #[ensures(result.len() == slice.len() - self.start)]
    fn index(self, slice: &[T]) -> &[T];
}

#[extern_spec]
impl<T> SliceIndex<[T]> for RangeTo<usize> {
    #[trusted]
    #[pure]
    #[ensures(result.len() == self.end)]
    fn index(self, slice: &[T]) -> &[T];
}

#[extern_spec]
impl<T> SliceIndex<[T]> for RangeFull {
    #[trusted]
    #[pure]
    #[ensures(result.len() == slice.len())]
    fn index(self, slice: &[T]) -> &[T];
}

#[extern_spec]
impl<T> SliceIndex<[T]> for RangeToInclusive<usize> {
    #[trusted]
    #[pure]
    #[ensures(result.len() == self.end + 1)]
    fn index(self, slice: &[T]) -> &[T];
}

#[extern_spec]
impl<T> SliceIndex<[T]> for RangeInclusive<usize> {
    #[trusted]
    #[pure]
    // Unsound for exhausted ranges (e.g. after iterating to the end), which
    // index to an empty slice; the private `exhausted` flag is not modelled.
    #[ensures(result.len() == *self.end() - *self.start() + 1)]
    fn index(self, slice: &[T]) -> &[T];
}

#[extern_spec]
impl<Idx> RangeInclusive<Idx> {
    #[trusted]
    #[pure]
    #[ensures(*result.start() === start)]
    #[ensures(*result.end() === end)]
    fn new(start: Idx, end: Idx) -> Self;

    #[trusted]
    #[pure]
    fn start(&self) -> &Idx;

    #[trusted]
    #[pure]
    fn end(&self) -> &Idx;
}
