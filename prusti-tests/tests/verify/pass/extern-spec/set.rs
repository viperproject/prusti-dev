extern crate prusti_contracts;
use prusti_contracts::*;

use std::collections::HashSet;
use std::borrow::Borrow;
use std::hash::Hash;
use std::cmp::Eq;
use std::option::Option;

#[extern_spec]
impl<T> Option<T> {
    #[pure]
    #[ensures(matches!(*self, Some(_)) == result)]
    pub fn is_some(&self) -> bool;

    #[pure]
    #[ensures(result != self.is_some())]
    pub fn is_none(&self) -> bool;

    #[requires(self.is_some())]
    pub fn unwrap(self) -> T;
}


#[extern_spec]
impl<T> HashSet::<T>
    where T: Eq, T: Hash {
    #[ensures(result.len() == 0)]
    pub fn new() -> HashSet<T>;

    #[pure]
    pub fn len(&self) -> usize;

    #[pure]
    pub fn contains<Q: ?Sized>(&self, value: &Q) -> bool
        where
            T: std::borrow::Borrow<Q>,
            Q: std::hash::Hash + std::cmp::Eq;

    #[ensures(self.len() == 0)]
    pub fn clear(&mut self);

    #[ensures(self.len() == 0 ==> result)]
    #[ensures(self.len() != 0 ==> !result)]
    pub fn is_empty(&self) -> bool;

    #[ensures(self.len() == old(self.len()) + 1)]
    pub fn insert(&mut self, value: T) -> bool;
}

fn main() {}
