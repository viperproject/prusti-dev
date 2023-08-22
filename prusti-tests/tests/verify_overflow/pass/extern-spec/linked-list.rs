#![feature(allocator_api)]

use prusti_contracts::*;

use std::collections::LinkedList;
use std::option::Option;

#[extern_spec]
impl<T> std::option::Option<T> {
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

/// Ghost method for LinkedList used to access an index in the LinkedList
#[trusted]
#[pure]
#[requires(index < list.len())]
fn get<T: Copy, A: std::alloc::Allocator + Clone>(list: &LinkedList<T, A>, index: usize) -> T {
    for (i, elem) in list.iter().enumerate() {
        if i == index {
            return *elem;
        }
    }
    unreachable!()
}

#[extern_spec]
impl<T> LinkedList<T, std::alloc::Global>
    where T: Copy + PartialEq {
    #[ensures(result.is_empty())]
    pub fn new() -> LinkedList<T, std::alloc::Global>;

    #[ensures(self.len() == old(self.len() + other.len()))]
    #[ensures(forall (|i: usize| (i < old(self.len())) ==>
        get(self, i) == old(get(self, i))))]
    #[ensures(forall (|j: usize| (old(self.len()) <= j && j < self.len()) ==>
        get(self, j) == old(get(other, j - self.len()))))]
    #[ensures(other.len() == 0)]
    pub fn append(&mut self, other: &mut LinkedList<T, std::alloc::Global>);
}

#[extern_spec]
impl<T, A> LinkedList<T, A>
    where T: Copy + PartialEq,
          A: std::alloc::Allocator + Clone {
    #[pure]
    #[ensures(result ==> self.len() == 0)]
    #[ensures(!result ==> self.len() > 0)]
    pub fn is_empty(&self) -> bool;

    #[pure]
    pub fn len(&self) -> usize;

    #[ensures(self.len() == 0)]
    pub fn clear(&mut self);

    #[ensures(self.len() == old(self.len()) + 1)]
    #[ensures(get(self, 0) == elt)]
    #[ensures(forall (|i: usize| (i < old(self.len())) ==>
        get(self, i + 1) == old(get(self, i))))]
    pub fn push_front(&mut self, elt: T);

    #[ensures(old(self.len()) == 0 ==> (self.len() == old(self.len())) && result.is_none())]
    #[ensures(old(self.len()) > 0 ==> self.len() == old(self.len()) - 1 && result.is_some())]
    #[ensures(old(self.len()) > 0 ==> forall (|i: usize| (i < self.len()) ==>
    get(self, i) == old(get(self, i + 1))))]
    pub fn pop_front(&mut self) -> Option<T>;

    #[ensures(self.len() == old(self.len()) + 1)]
    #[ensures(get(self, self.len() - 1) == elt)]
    #[ensures(forall (|i: usize| (i < old(self.len())) ==>
    get(self, i) == old(get(self, i))))]
    pub fn push_back(&mut self, elt: T);

    #[ensures(old(self.len()) == 0 ==> (self.len() == old(self.len())) && result.is_none())]
    #[ensures(old(self.len()) > 0 ==> self.len() == old(self.len()) - 1 && result.is_some())]
    #[ensures(old(self.len()) > 0 ==> forall (|i: usize| (i < self.len()) ==>
    get(self, i) == old(get(self, i))))]
    pub fn pop_back(&mut self) -> Option<T>;

    #[requires(at <= self.len())]
    #[ensures(result.len() == old(self.len()) - at)]
    #[ensures(self.len() == at)]
    #[ensures(forall (|i: usize| (i < self.len()) ==>
        get(self, i) == old(get(self, i))))]
    #[ensures(forall (|j: usize| (j < result.len()) ==>
        get(&result, j) == old(get(self, j + at))))]
    pub fn split_off(&mut self, at: usize) -> LinkedList<T, A>;
}

fn main() {
    let mut l = LinkedList::new();
    l.push_front(1);

    assert!(get(&l, 0) == 1);

    let mut ll2 = LinkedList::new();
    ll2.push_front(2);
    ll2.push_front(3);
    ll2.push_front(4);
    assert!(get(&ll2, 2) == 2);
    assert!(get(&ll2, 1) == 3);
    assert!(get(&ll2, 0) == 4);

    l.append(&mut ll2);
    assert!(l.len() == 4);

    assert!(get(&l, 3) == 2);
    assert!(get(&l, 2) == 3);
    assert!(get(&l, 1) == 4);

    assert!(matches!(l.pop_front(), Some(1)));

    assert!(l.len() == 3);
}
