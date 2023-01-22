use prusti_contracts::*;

use std::{
    borrow::Borrow,
    cmp::Eq,
    collections::HashSet,
    hash::{BuildHasher, Hash},
    option::Option,
};

#[extern_spec]
impl<T> HashSet<T> {
    #[ensures(result.len() == 0)]
    pub fn new() -> HashSet<T>;
}

#[extern_spec]
impl<T, S> HashSet<T, S> {
    #[pure]
    pub fn len(&self) -> usize;

    #[ensures(self.len() == 0)]
    pub fn clear(&mut self);

    #[ensures(self.len() == 0 ==> result)]
    #[ensures(self.len() != 0 ==> !result)]
    pub fn is_empty(&self) -> bool;
}

#[extern_spec]
impl<T, S> HashSet<T, S>
where
    T: Eq + Hash,
    S: BuildHasher,
{
    #[pure]
    pub fn contains<Q: ?Sized>(&self, value: &Q) -> bool
    where
        T: std::borrow::Borrow<Q>,
        Q: std::hash::Hash + std::cmp::Eq;

    #[ensures(self.len() == old(self.len()) + 1)]
    pub fn insert(&mut self, value: T) -> bool;
}

fn main() {}
