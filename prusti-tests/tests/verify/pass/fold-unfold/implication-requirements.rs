//! From https://github.com/viperproject/prusti-dev/issues/471

use prusti_contracts::*;
use std::collections::HashSet;

struct TwoPSet {
    add_set: HashSet<u64>,
    remove_set: HashSet<u64>,
}

#[extern_spec]
impl HashSet<u64> {
    #[pure]
    pub fn contains(&self, value: &u64) -> bool;
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
