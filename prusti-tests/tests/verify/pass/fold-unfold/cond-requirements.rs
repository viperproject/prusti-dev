//! From https://github.com/viperproject/prusti-dev/issues/471
#![feature(allocator_api)]

use prusti_contracts::*;
use std::{alloc::Allocator, collections::HashSet};

struct TwoPSet {
    remove_set: HashSet<u64>,
}

#[extern_spec]
impl<T, S, A> HashSet<T, S, A>
where
    T: Eq + std::hash::Hash,
    S: std::hash::BuildHasher,
    A: Allocator,
{
    #[trusted]
    #[pure]
    pub fn contains<Q: ?Sized>(&self, value: &Q) -> bool
    where
        T: std::borrow::Borrow<Q>,
        Q: std::hash::Hash + Eq;
}

impl TwoPSet {
    #[trusted]
    #[pure]
    fn length(&self) -> usize {
        unimplemented!()
    }

    #[ensures(result == false ==> self.remove_set.contains(&val))]
    #[ensures(self.length() == self.length() + 0)]
    fn add(&mut self, val: u64) -> bool {
        if self.remove_set.contains(&val) {
            false
        } else {
            true
        }
    }
}

fn main() {}
