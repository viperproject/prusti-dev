#![feature(register_tool)]
#![register_tool(prusti)]

extern crate prusti_contracts;
use prusti_contracts::*;

use std::ops::Index;
use std::vec::Vec;

/// Example specifying trait implementations

#[extern_spec]
impl<T> Vec::<T> {
    #[ensures(true)]
    fn clone(&self) -> Vec::<T>
        where T: std::clone::Clone;

    /// Currently uses an unsupported type and will panic during type encoding
    #[pure]
    fn index<Idx>(&self, index: Idx) -> &<Vec::<T> as Index::<Idx>>::Output
        where Idx: std::slice::SliceIndex<[T]>;
}

fn main() {}
