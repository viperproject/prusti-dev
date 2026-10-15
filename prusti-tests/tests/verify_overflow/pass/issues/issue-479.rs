#![feature(allocator_api)]

use prusti_contracts::*;
use std::{
    collections::HashMap,
    hash::{BuildHasher, Hash},
};

#[extern_spec]
impl<K, V, S, A> HashMap<K, V, S, A>
where
    A: std::alloc::Allocator,
{
    #[trusted]
    #[pure]
    fn len(&self) -> usize;
}

#[extern_spec]
impl<K, V, S, A> HashMap<K, V, S, A>
where
    K: Eq + Hash,
    S: BuildHasher,
    A: std::alloc::Allocator,
{
    #[trusted]
    #[ensures(result === None ==> self.len() == old(self.len()) + 1)]
    fn insert(&mut self, key: K, value: V) -> Option<V>;
}

fn test(mut x: HashMap<u64, u64>) {
    let orig_len = x.len();
    if let None = x.insert(234, 345) {
        assert!(x.len() == orig_len + 1);
    }
}

#[trusted]
fn main() {}
