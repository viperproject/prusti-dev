// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

// This version will compile with prusti-rustc but uses various partially
// supported features. Attempting to verify anything might crash Prusti.

extern crate prusti_contracts;

use std::collections::HashMap;
use std::hash::Hash;

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct Locator(usize);

const NUM_PAGES: usize = 512usize;

#[derive(Clone)]
pub struct Page<T: Clone> {
    data: T,
    next:  Option<usize>,
}

#[derive(Clone)]
pub struct VecWrapper<T: Clone> {
    v: Vec<T>,
}

pub struct HashMapLocatorWrapper {
    m: HashMap<Locator, Locator>,
}

impl HashMapLocatorWrapper {
    #[trusted]
    pub fn get(&self, k: &Locator) -> Option<Locator>{
        unimplemented!()
    }

    #[trusted]
    #[pure]
    pub fn contains_kv(&self, k: &Locator, v: usize) -> bool {
       unimplemented!()
    }

    #[trusted]
    #[ensures="old(self.contains_kv(k, 0))"]
    pub fn remove(&mut self, k: &Locator) -> Option<Locator> {
        unimplemented!()
    }
}


struct Disk<T: Clone> {
    pages: VecWrapper<Page<T>>,
}

impl<T: Clone> Disk<T> {
    fn read(&self, p: usize) -> Page<T> {
        unimplemented!()
    }
}

pub struct KeyStore<T: Clone> {
    disk: Disk<T>,
    predecessor: HashMapLocatorWrapper,
}

impl<T: Eq + Hash + Clone> KeyStore<T> {
    pub fn delete(&mut self, locator: Locator) {
        if let Some(loc) = self.predecessor.get(&locator) {
            let this_page = self.disk.read(locator.0);
            self.predecessor.remove(&locator);
        }
    }
}

fn main() {}
