//! From https://github.com/viperproject/prusti-dev/issues/471

use prusti_contracts::*;
use std::collections::HashSet;

struct TwoPSet {
    remove_set: HashSet<u64>,
}

#[extern_spec]
impl<T, S> HashSet<T, S>
where
    T: Eq + std::hash::Hash,
    S: std::hash::BuildHasher,
{
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
