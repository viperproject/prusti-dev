use prusti_contracts::*;

use std::collections::HashSet;
use std::hash::Hash;
use std::cmp::Eq;

struct SetWrapper<T: Hash + Eq> {
    set: HashSet<T>
}

impl<T: Hash + Eq> SetWrapper<T> {
    #[pure]
    #[trusted]
    pub fn contains(&self, value: &T) -> bool {
        self.set.contains(value)
    }

    #[ensures(self.contains(&old(value)))]
    #[trusted]
    pub fn insert(&mut self, value: T) {
        self.set.insert(value);
    }

    #[ensures(!self.contains(old(value)))]
    #[trusted]
    pub fn remove(&mut self, value: &T) -> bool {
        self.set.remove(value)
    }
}

fn main() {
    let mut set = SetWrapper { set: HashSet::new() };
    set.insert(1);
    set.insert(2);
    set.insert(3);

    // TODO: the local variable is required for now
    let three = 3;
    set.remove(&three);
    let two = 2;
    set.remove(&two);
    let one = 1;
    set.remove(&one);
    set.remove(&one);
}
