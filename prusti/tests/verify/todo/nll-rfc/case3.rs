/// Problem case #3: conditional control flow across functions
///
/// Adapted from
/// [here](https://github.com/nikomatsakis/nll-rfc/blob/master/0000-nonlexical-lifetimes.md).
///
/// TODO: Add specifications.

extern crate prusti_contracts;

use std::collections::HashMap;

pub struct HashMapWrapperI32 {
    map: HashMap<i32, i32>,
}

impl HashMapWrapperI32 {
    #[trusted]
    pub fn new() -> Self {
        HashMapWrapperI32{ map: HashMap::new() }
    }
    #[trusted]
    pub fn get_mut(&mut self, key: &mut i32) -> Option<&mut i32> {
        self.map.get_mut(key)
    }
    #[trusted]
    pub fn insert(&mut self, key: i32, value: i32) {
        self.map.insert(key, value);
    }
}

fn get_default<'r>(map: &'r mut HashMapWrapperI32, key: i32) -> &'r mut i32 {
    let mut key = key;
    match map.get_mut(&mut key) {
        Some(value) => value,
        None => {
            map.insert(key, 0);
            map.get_mut(&mut key).unwrap()
        }
    }
}

fn main() {
}
