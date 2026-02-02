// ignore-test: slicing with RangeInclusive (e.g. [x..=y]) currently not supported

#![feature(const_panic)]
#![feature(slice_index_methods)]

use prusti_contracts::*;

// #[extern_spec]
// impl std::ops::RangeInclusive<usize> {
//     #[ensures(*result.start() == start)]
//     #[ensures(*result.end() == end)]
//     pub const fn new(start: usize, end: usize) -> std::ops::RangeInclusive<usize>;

//     #[pure]
//     pub const fn start(&self) -> &usize;
//     #[pure]
//     pub const fn end(&self) -> &usize;
// }

#[extern_spec]
impl<T> std::slice::SliceIndex<[T]> for std::ops::Range<usize> {
    #[ensures( result.len() == self.end - self.start )]
    #[ensures( forall(|i: usize| (0 <= i && i < result.len()) ==> result[i] === slice[i+self.start]) )]
    fn index(self, slice: &[T]) -> &[T];
}

#[extern_spec]
impl<T, I: std::slice::SliceIndex<[T]>> std::ops::Index<I> for [T] {
    #[ensures( result === <I as std::slice::SliceIndex<[T]>>::index(index, self) )]
    fn index(&self, index: I) -> &I::Output;
}

fn main() {}

#[requires(a.len() > 6)]
fn slice(a: &[i32]) {
    let s = &a[1..4];
    assert!(s[0] == a[1]);

    /*
    let s = &a[..2];
    assert!(s[1] == a[1]);
    let s = &a[1..];
    assert!(s[2] == a[3]);
    let s = &a[..];
    assert!(s[3] == a[3]);*/

    // let s = &a[1..=4];
    // assert!(s[3] == a[4]);

    /*let s = &a[..=5];
    assert!(s[5] == a[5]);*/
}
