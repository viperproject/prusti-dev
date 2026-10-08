use crate::*;

use core::{
    ops::{Range, RangeFrom, RangeFull, RangeInclusive, RangeTo, RangeToInclusive},
    slice::SliceIndex,
};

#[extern_spec]
impl<T> SliceIndex<[T]> for Range<usize> {
    #[trusted]
    #[pure]
    #[ensures(self.start <= self.end && self.end <= slice.len() ==> result.len() == self.end - self.start)]
    fn index(self, slice: &[T]) -> &[T];
}

#[extern_spec]
impl<T> SliceIndex<[T]> for RangeFrom<usize> {
    #[trusted]
    #[pure]
    #[ensures(self.start <= slice.len() ==> result.len() == slice.len() - self.start)]
    fn index(self, slice: &[T]) -> &[T];
}

#[extern_spec]
impl<T> SliceIndex<[T]> for RangeTo<usize> {
    #[trusted]
    #[pure]
    #[ensures(self.end <= slice.len() ==> result.len() == self.end)]
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
    #[ensures(self.end < slice.len() ==> result.len() == self.end + 1)]
    fn index(self, slice: &[T]) -> &[T];
}
