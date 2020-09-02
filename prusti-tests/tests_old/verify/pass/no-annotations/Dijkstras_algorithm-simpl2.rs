//! An adaptation of the example from
//! https://rosettacode.org/wiki/Dijkstra%27s_algorithm#Rust

extern crate prusti_contracts;

use std::cmp::Ordering;
use std::collections::BinaryHeap;
use std::usize;


struct VecWrapperPath{
    v: Vec<usize>
}

impl VecWrapperPath {
    #[trusted]
    pub fn new() -> Self {
        unimplemented!()
    }
}

fn find_path() -> Option<VecWrapperPath> {
    let mut result = None;
    while true {
        let path = VecWrapperPath::new();
        result = Some(path);
    }
    result
}

fn main() {}
