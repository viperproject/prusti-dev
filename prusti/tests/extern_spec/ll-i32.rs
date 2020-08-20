#![feature(register_tool)]
#![register_tool(prusti)]

extern crate prusti_contracts;
use prusti_contracts::*;

use std::collections::LinkedList;
use std::option::Option;

#[extern_spec]
impl<T> std::option::Option::<T> {
    #[pure]
    #[ensures(matches!(*self, Some(_)) == result)]
    pub fn is_some(&self) -> bool;

    #[pure]
    #[ensures(self.is_some() == !result)]
    pub fn is_none(&self) -> bool;

    #[requires(self.is_some())]
    pub fn unwrap(self) -> T;

    #[requires(self.is_some())]
    pub fn expect(self, msg: &str) -> T;
}

#[extern_spec]
impl LinkedList::<i32> {
    #[ensures(result.is_empty())]
    pub fn new() -> LinkedList<i32>;

    #[pure]
    #[ensures(self.len() == 0)]
    pub fn is_empty(&self) -> bool;

    #[ensures(self.len() == old(self.len() + other.len()))]
    pub fn append(&mut self, other: &mut LinkedList<i32>);

    #[pure]
    pub fn len(&self) -> usize;

    #[ensures(self.len() == 0)]
    pub fn clear(&mut self);

    #[ensures(self.len() == old(self.len()) + 1)]
    pub fn push_front(&mut self, elt: i32);

    #[ensures(old(self.len()) > 0 ==> self.len() == old(self.len()) - 1 && result.is_some())]
    #[ensures(old(self.len()) == 0 ==> (self.len() == old(self.len())) && result.is_none())]
    pub fn pop_front(&mut self) -> Option<i32>;
}

#[extern_spec]
impl<T> LinkedList::<T> {
    #[ensures(result.is_empty())]
    pub fn new() -> LinkedList<T>;
}

fn main() {
    let mut l = LinkedList::new();
    l.push_front(1);

    let mut ll2 = LinkedList::new();
    ll2.push_front(2);
    ll2.push_front(3);
    ll2.push_front(4);

    l.append(&mut ll2);
    assert!(l.len() == 4);

    l.pop_front();

    assert!(l.len() == 3);
}
