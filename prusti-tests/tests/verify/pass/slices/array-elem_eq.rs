#![feature(const_panic)]

use prusti_contracts::*;

#[extern_spec]
impl std::ops::RangeInclusive<usize> {
    #[ensures(*result.start() == start)]
    #[ensures(*result.end() == end)]
    pub const fn new(start: usize, end: usize) -> std::ops::RangeInclusive<usize>;

    #[pure]
    pub const fn start(&self) -> &usize;
    #[pure]
    pub const fn end(&self) -> &usize;
}

fn main() {}

fn slice(a: &[i32; 6]) {
    /*
    let s = &a[1..4];
    assert!(s[0] == a[1]);
    let s = &a[..2];
    assert!(s[1] == a[1]);
    let s = &a[1..];
    assert!(s[2] == a[3]);
    let s = &a[..];
    assert!(s[3] == a[3]);*/
    let s = &a[1..=4];
    assert!(s[3] == a[4]);
    /*let s = &a[..=5];
    assert!(s[5] == a[5]);*/
}
