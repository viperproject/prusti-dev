#![feature(allocator_api)]

use prusti_contracts::*;

use std::{
    borrow::Borrow,
    cmp::Eq,
    collections::HashSet,
    hash::{BuildHasher, Hash},
    option::Option,
};

#[extern_spec]
impl<T> Option<T> {
    #[trusted]
    #[pure]
    #[ensures(matches!(*self, Some(_)) == result)]
    pub fn is_some(&self) -> bool;

    #[trusted]
    #[pure]
    #[ensures(result != self.is_some())]
    pub fn is_none(&self) -> bool;

    #[trusted]
    #[requires(self.is_some())]
    pub fn unwrap(self) -> T;
}

#[extern_spec]
impl<T> HashSet<T> {
    #[trusted]
    #[ensures(result.len() == 0)]
    pub fn new() -> HashSet<T>;
}

#[extern_spec]
impl<T, S, A> HashSet<T, S, A>
where
    A: std::alloc::Allocator,
{
    #[trusted]
    #[pure]
    pub fn len(&self) -> usize;

    #[trusted]
    #[ensures(self.len() == 0)]
    pub fn clear(&mut self);

    #[trusted]
    #[ensures(self.len() == 0 ==> result)]
    #[ensures(self.len() != 0 ==> !result)]
    pub fn is_empty(&self) -> bool;
}

#[extern_spec]
impl<T, S, A> HashSet<T, S, A>
where
    T: Eq + Hash,
    S: BuildHasher,
    A: std::alloc::Allocator,
{
    #[trusted]
    #[pure]
    pub fn contains<Q: ?Sized>(&self, value: &Q) -> bool
    where
        T: std::borrow::Borrow<Q>,
        Q: std::hash::Hash + std::cmp::Eq;

    #[trusted]
    #[ensures(self.len() == old(self.len()) + 1)]
    pub fn insert(&mut self, value: T) -> bool;
}

fn main() {}
