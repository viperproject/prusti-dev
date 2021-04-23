//! From https://github.com/viperproject/prusti-dev/issues/471
//! From https://github.com/viperproject/prusti-dev/issues/471

use prusti_contracts::*;
use std::collections::HashSet;

struct TwoPSet {
    remove_set: HashSet<u64>,
}

#[extern_spec]
impl HashSet<u64> {
    #[pure]
    pub fn contains(&self, value: &u64) -> bool;
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
