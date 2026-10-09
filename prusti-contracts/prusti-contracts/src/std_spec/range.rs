use crate::{core_spec::slice::slice_index_touches, *};

use core::{
    ops::{Range, RangeFrom, RangeFull, RangeInclusive, RangeTo, RangeToInclusive},
    slice::SliceIndex,
};

#[extern_spec]
impl<T> SliceIndex<[T]> for Range<usize> {
    #[trusted]
    #[pure]
    #[ensures(slice_index_touches(&self, 0) == (self.start <= 0 && 0 < self.end))]
    #[ensures(slice_index_touches(&self, 1) == (self.start <= 1 && 1 < self.end))]
    #[ensures(slice_index_touches(&self, 2) == (self.start <= 2 && 2 < self.end))]
    #[ensures(self.start <= self.end && self.end <= slice.len() ==> result.len() == self.end - self.start)]
    fn index(self, slice: &[T]) -> &[T];
}

#[extern_spec]
impl<T> SliceIndex<[T]> for RangeFrom<usize> {
    #[trusted]
    #[pure]
    #[ensures(slice_index_touches(&self, 0) == (self.start <= 0))]
    #[ensures(slice_index_touches(&self, 1) == (self.start <= 1))]
    #[ensures(slice_index_touches(&self, 2) == (self.start <= 2))]
    #[ensures(self.start <= slice.len() ==> result.len() == slice.len() - self.start)]
    fn index(self, slice: &[T]) -> &[T];
}

#[extern_spec]
impl<T> SliceIndex<[T]> for RangeTo<usize> {
    #[trusted]
    #[pure]
    #[ensures(slice_index_touches(&self, 0) == (0 < self.end))]
    #[ensures(slice_index_touches(&self, 1) == (1 < self.end))]
    #[ensures(slice_index_touches(&self, 2) == (2 < self.end))]
    #[ensures(self.end <= slice.len() ==> result.len() == self.end)]
    fn index(self, slice: &[T]) -> &[T];
}

#[extern_spec]
impl<T> SliceIndex<[T]> for RangeFull {
    #[trusted]
    #[pure]
    #[ensures(slice_index_touches(&self, 0) == (true))]
    #[ensures(slice_index_touches(&self, 1) == (true))]
    #[ensures(slice_index_touches(&self, 2) == (true))]
    #[ensures(result.len() == slice.len())]
    fn index(self, slice: &[T]) -> &[T];
}

#[extern_spec]
impl<T> SliceIndex<[T]> for RangeToInclusive<usize> {
    #[trusted]
    #[pure]
    #[ensures(slice_index_touches(&self, 0) == (0 <= self.end))]
    #[ensures(slice_index_touches(&self, 1) == (1 <= self.end))]
    #[ensures(slice_index_touches(&self, 2) == (2 <= self.end))]
    #[ensures(self.end < slice.len() ==> result.len() == self.end + 1)]
    fn index(self, slice: &[T]) -> &[T];
}
