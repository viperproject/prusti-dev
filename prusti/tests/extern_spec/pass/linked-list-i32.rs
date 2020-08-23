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

/// Ghost method for LinkedList used to access an index in the LinkedList
#[trusted]
#[pure]
#[requires(index < list.len())]
fn get(list: &LinkedList<i32>, index: usize) -> i32 {
    for (i, elem) in list.iter().enumerate() {
        if i == index {
            return *elem;
        }
    }
    unreachable!()
}

/// Using i32 instead of a generic type because Prusti does not currently support it.
/// However, it is not possible to define specifications for different variants of the same type and if
/// attempted, will result in an error indicating duplicate specifications.
#[extern_spec]
impl LinkedList::<i32> {
    #[ensures(result.is_empty())]
    pub fn new() -> LinkedList<i32>;

    #[ensures(self.len() == old(self.len() + other.len()))]
    #[ensures(forall (|i: usize| (0 <= i && i < old(self.len())) ==>
    get(self, i) == old(get(self, i))))]
    #[ensures(forall (|j: usize| (0 <= j && j < old(other.len())) ==>
    get(self, j + old(self.len())) == old(get(other, j))))]
    pub fn append(&mut self, other: &mut LinkedList<i32>);

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
    #[ensures(forall (|i: usize| (0 <= i && i < old(self.len())) ==>
    get(self, i + 1) == old(get(self, i))))]
    pub fn push_front(&mut self, elt: i32);

    #[ensures(old(self.len()) == 0 ==> (self.len() == old(self.len())) && result.is_none())]
    #[ensures(old(self.len()) > 0 ==> self.len() == old(self.len()) - 1 && result.is_some())]
    #[ensures(old(self.len()) > 0 ==> forall (|i: usize| (0 <= i && i < self.len()) ==>
    get(self, i) == old(get(self, i + 1))))]
    pub fn pop_front(&mut self) -> Option<i32>;

    #[ensures(self.len() == old(self.len()) + 1)]
    #[ensures(get(self, self.len() - 1) == elt)]
    #[ensures(forall (|i: usize| (0 <= i && i < old(self.len())) ==>
    get(self, i) == old(get(self, i))))]
    pub fn push_back(&mut self, elt: i32);

    #[ensures(old(self.len()) == 0 ==> (self.len() == old(self.len())) && result.is_none())]
    #[ensures(old(self.len()) > 0 ==> self.len() == old(self.len()) - 1 && result.is_some())]
    #[ensures(old(self.len()) > 0 ==> forall (|i: usize| (0 <= i && i < self.len()) ==>
    get(self, i) == old(get(self, i))))]
    pub fn pop_back(&mut self) -> Option<i32>;

    #[requires(at <= self.len())]
    #[ensures(result.len() == old(self.len()) - at)]
    #[ensures(self.len() == at)]
    #[ensures(forall (|i: usize| (0 <= i && i < self.len()) ==>
    get(self, i) == old(get(self, i))))]
    #[ensures(forall (|j: usize| (0 <= j && j < result.len()) ==>
    get(&result, j) == old(get(self, j + at))))]
    pub fn split_off(&mut self, at: usize) -> LinkedList<i32>;
}

#[requires(index >= 0 && index <= list.len())]
#[ensures(list.len() == old(list.len()) + 1)]
#[ensures(forall (|i: usize| (0 < i && i < index && i < old(list.len())) ==>
get(list, i) == old(get(list, i))))]
#[ensures(get(list, index) == val)]
/// The following post-condition may not hold because of the else block (split_off, append)
// #[ensures(forall (|j: usize| (index < j && j < list.len()) ==>
//     get(list, j) == old(get(list, j - 1))))]
fn insert(list: &mut LinkedList<i32>, index: usize, val:i32) {
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

/// Iterative version of reverse. Cannot add specifications because
/// loop invariants are currently not supported
fn reverse(list: &mut LinkedList<i32>) {
    let mut stack = LinkedList::new();
    while !list.is_empty() {
        let first = list.pop_front();
        // Needed because loop invariants currently not working
        if first.is_some() {
            stack.push_back(first.unwrap());
        }
    }

    while !stack.is_empty() {
        let last = stack.pop_back();
        // Needed because loop invariants currently not working
        if last.is_some() {
            list.push_back(last.unwrap());
        }
    }
}


/// This wrapper is needed because Prusti crashes with an access error when
/// trying to encode the actual clone method (needs &mut instead of & for some reason)
#[trusted]
#[ensures(list.len() == old(list.len()))]
#[ensures(list.len() == result.len())]
#[ensures(forall (|i: usize| (0 <= i && i < list.len()) && i < old(list.len())==>
get(list, i) == old(get(list, i))))]
#[ensures(forall (|j: usize| (0 <= j && j < result.len() && j < list.len()) ==>
get(&result, j) == get(list, j)))]
fn clone(list: &mut LinkedList<i32>) -> LinkedList<i32> {
    list.clone()
}

/// Recursive version of reverse
#[ensures(list.len() == old(list.len()))]
fn recursive_reverse(list: &mut LinkedList<i32>) {
    let mut stack = clone(list);
    list.clear();
    reverse_helper(list, &mut stack);
}

#[ensures(list.len() == old(stack.len() + list.len()))]
#[ensures(forall (|i: usize| (0 <= i && i < old(list.len()) && i < list.len()) ==>
get(list, i) == old(get(list, i))))]
/// The following post-condition does not hold
// #[ensures(forall (|j: usize| (0 <= j && j < old(stack.len())) ==>
//     get(list, list.len() - 1 - j) == old(get(stack, j))))]
fn reverse_helper(list: &mut LinkedList<i32>, stack: &mut LinkedList<i32>) {
    if !stack.is_empty() {
        list.push_back(stack.pop_back().unwrap());
        reverse_helper(list, stack);
    }
}

fn main() {}
