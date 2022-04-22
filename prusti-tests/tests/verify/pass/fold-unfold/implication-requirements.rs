//! From https://github.com/viperproject/prusti-dev/issues/471

use prusti_contracts::*;
use std::collections::HashSet;

struct TwoPSet {
    add_set: HashSet<u64>,
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
    #[ensures(!result ==> self.remove_set.contains(&val))]
    fn add(&mut self, val: u64) -> bool {
        if self.remove_set.contains(&val) {
            false
        } else {
            self.add_set.insert(val);
            true
        }
    }
}

fn main() {}
