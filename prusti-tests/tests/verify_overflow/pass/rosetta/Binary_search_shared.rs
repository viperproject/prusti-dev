//! A version of `Binary_search.rs` that uses shared references.

#![allow(dead_code)]
use prusti_contracts::*;

pub struct VecWrapperI32{
    v: Vec<i32>
}

impl VecWrapperI32 {
    #[trusted]
    #[pure]
    pub fn len(&self) -> usize {
        self.v.len()
    }

    #[trusted]
    #[ensures(result.len() == 0)]
    pub fn new() -> Self {
        VecWrapperI32{ v: Vec::new() }
    }

    #[trusted]
    #[pure]
    #[requires(0 <= index && index < self.len())]
    pub fn lookup(&self, index: usize) -> i32 {
        self.v[index]
    }

    #[trusted]
    #[requires(0 <= index && index < self.len())]
    #[ensures(*result == old(self.lookup(index)))]
    #[after_expiry(
        self.len() == old(self.len()) &&
        self.lookup(index) == before_expiry(*result) &&
        forall(|i: usize| (0 <= i && i < self.len() && i != index) ==>
            self.lookup(i) == old(self.lookup(i)))
    )]
    pub fn borrow(&self, index: usize) -> &i32 {
        self.v.get(index).unwrap()
    }

    #[trusted]
    #[ensures(self.len() == old(self.len()) + 1)]
    #[ensures(self.lookup(old(self.len())) == value)]
    #[ensures(forall(|i: usize| (0 <= i && i < old(self.len())) ==>
                    self.lookup(i) == old(self.lookup(i))))]
    pub fn push(&mut self, value: i32) {
        self.v.push(value);
    }
}

enum UsizeOption {
    Some(usize),
    None,
}

impl UsizeOption {
    #[pure]
    fn is_some(&self) -> bool {
        match self {
            UsizeOption::Some(_) => true,
            UsizeOption::None => false,
        }
    }
    #[pure]
    fn is_none(&self) -> bool {
        !self.is_some()
    }
    #[pure]
    #[requires(self.is_some())]
    fn peek(&self) -> usize {
        match self {
            UsizeOption::Some(n) => *n,
            UsizeOption::None => unreachable!(),
        }
    }
}

pub enum Ordering {
    Less,
    Equal,
    Greater,
}

use self::Ordering::*;

#[ensures((match result {
                Equal => a == b,
                Less => a < b,
                Greater => a > b,
            }))]
fn cmp(a: i32, b: i32) -> Ordering {
    if a == b { Equal }
    else if a < b { Less }
    else { Greater }
}

#[requires(forall(|k1: usize, k2: usize| (0 <= k1 && k1 < k2 && k2 < arr.len()) ==>
             arr.lookup(k1) <= arr.lookup(k2)))]
#[ensures(arr.len() == old(arr.len()))]
#[ensures(forall(|k: usize| (0 <= k && k < arr.len()) ==> arr.lookup(k) == old(arr.lookup(k))))]
#[ensures(result.is_none() ==>
            forall(|k: usize| (0 <= k && k < arr.len()) ==> elem != arr.lookup(k)))]
#[ensures(result.is_some() ==> (
                0 <= result.peek() && result.peek() < arr.len() &&
                arr.lookup(result.peek()) == elem))]
fn binary_search(arr: &VecWrapperI32, elem: i32) -> UsizeOption
{
    let mut size = arr.len();
    let mut base = 0;

    let mut result = UsizeOption::None;
    let mut continue_loop = size > 0;

    while continue_loop {
        body_invariant!(base + size <= arr.len());
        body_invariant!(size > 0 && result.is_none());
        body_invariant!(arr.len() == old(arr.len()));
        body_invariant!(forall(|k1: usize, k2: usize| (0 <= k1 && k1 < k2 && k2 < arr.len()) ==>
            arr.lookup(k1) <= arr.lookup(k2)));
        body_invariant!(forall(|k: usize| (0 <= k && k < arr.len()) ==> arr.lookup(k) == old(arr.lookup(k))));
        body_invariant!(forall(|k: usize| (0 <= k && k < base) ==> arr.lookup(k) < elem));
        body_invariant!(result.is_none() ==>
             forall(|k: usize| (base + size <= k && k < arr.len()) ==> elem < arr.lookup(k))
        );
        body_invariant!(result.is_some() ==> (
                0 <= result.peek() && result.peek() < arr.len() &&
                arr.lookup(result.peek()) == elem));
        let half = size / 2;
        let mid = base + half;

        let mid_element = arr.borrow(mid);
        let cmp_result = cmp(*mid_element, elem);
        base = match cmp_result {
            Less    => {
                mid
            },
            Greater => {
                base
            },
            // Equal
            _   => {
                result = UsizeOption::Some(mid);
                base   // Just return anything because we are finished.
            }
        };
        size -= half;
        continue_loop = size > 0 && result.is_none();
    }

    result
}

fn main() {}
