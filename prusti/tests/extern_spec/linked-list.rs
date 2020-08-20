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
impl<T> LinkedList::<T>
    where T: Copy + PartialEq {
    #[ensures(result.is_empty())]
    pub fn new() -> LinkedList<T>;

    #[ensures(self.len() == old(self.len() + other.len()))]
    pub fn append(&mut self, other: &mut LinkedList<T>);

    #[pure]
    #[ensures(self.len() == 0)]
    pub fn is_empty(&self) -> bool;

    #[pure]
    pub fn len(&self) -> usize;

    #[ensures(self.len() == 0)]
    pub fn clear(&mut self);

    #[ensures(self.len() == old(self.len()) + 1)]
    // #[ensures(LinkedListExtras::get(self, 0) == elt)]
    pub fn push_front(&mut self, elt: T);

    #[ensures(old(self.len()) > 0 ==> self.len() == old(self.len()) - 1 && result.is_some())]
    #[ensures(old(self.len()) == 0 ==> (self.len() == old(self.len())) && result.is_none())]
    pub fn pop_front(&mut self) -> Option<T>;

    #[ensures(self.len() == old(self.len()) + 1)]
    pub fn push_back(&mut self, elt: T);

    #[ensures(old(self.len()) > 0 ==> self.len() == old(self.len()) - 1 && result.is_some())]
    #[ensures(old(self.len()) == 0 ==> (self.len() == old(self.len())) && result.is_none())]
    pub fn pop_back(&mut self) -> Option<T>;

    #[ensures(result.len() == old(self.len()) - at)]
    #[ensures(self.len() == at)]
    pub fn split_off(&mut self, at: usize) -> LinkedList<T>;
}


struct LinkedListExtras<T>(std::marker::PhantomData<T>);

impl<T> LinkedListExtras<T> where T: Copy + PartialEq {
    #[requires(index >= 0 && index <= list.len())]
    #[ensures(list.len() == old(list.len()) + 1)]
    fn insert(list: &mut LinkedList<T>, index: usize, val: T) {
        if index == 0 {
            list.push_front(val);
        } else if index == list.len() {
            list.push_back(val);
        } else {
            let mut tail = list.split_off(index);
            list.push_back(val);
            list.append(&mut tail);
        }
    }

    #[trusted]
    #[pure]
    #[requires(index < list.len())]
    fn get(list: &mut LinkedList<T>, index: usize) -> T {
        for (i, elem) in list.iter().enumerate() {
            if i == index {
                return *elem;
            }
        }
        unreachable!()
    }
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
    // LinkedListExtras::insert(&mut l, 2, 4);
    // assert!(l.len() == 4);
}
