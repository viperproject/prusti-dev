// ignore-test: slicing with RangeInclusive (e.g. [x..=y]) currently not supported

#![feature(const_panic)]

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
impl<T> std::ops::Index<std::ops::Range<usize>> for [T] {
    #[ensures( result.len() == index.end - index.start )]
    #[ensures( forall(|i: usize| (0 <= i && i < result.len()) ==> result[i] == self[i+index.start]) )]
    fn index(&self, index: std::ops::Range<usize>) -> &[T];
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
