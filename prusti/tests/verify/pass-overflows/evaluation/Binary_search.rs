//! An adaptation of the example from
//! https://rosettacode.org/wiki/Binary_search#Rust
//!
//! Changes:
//!
//! +   Monomorphised types.
//! +   Wrapped built-in types and functions.
//! +   Replaced a slice with a reference into a vector.
//! +   Rewrote to remove a return statement.
//!
//! Verified properties:
//!
//! +   Absence of panics.
//! +   Absence of overflows.

extern crate prusti_contracts;

pub struct VecWrapperI32{
    v: Vec<i32>
}

impl VecWrapperI32 {
    #[trusted]
    #[pure]
    #[ensures="result >= 0"]
    #[ensures="result < 18446744073709551615"]
    pub fn len(&self) -> usize {
        self.v.len()
    }

    #[trusted]
    #[ensures="result.len() == 0"]
    pub fn new() -> Self {
        VecWrapperI32{ v: Vec::new() }
    }

    #[trusted]
    #[pure]
    #[requires="0 <= index && index < self.len()"]
    pub fn lookup(&self, index: usize) -> i32 {
        self.v[index]
    }

    #[trusted]
    #[requires="0 <= index && index < self.len()"]
    #[ensures="*result == old(self.lookup(index))"]
    #[ensures="after_expiry(
        self.len() == old(self.len()) &&
        self.lookup(index) == before_expiry(*result) &&
        (
            forall i: usize :: (0 <= i && i < self.len() && i != index) ==>
            self.lookup(i) == old(self.lookup(i))
        )
        )"]
    pub fn borrow(&mut self, index: usize) -> &mut i32 {
        self.v.get_mut(index).unwrap()
    }

    #[trusted]
    #[ensures="self.len() == old(self.len()) + 1"]
    #[ensures="self.lookup(old(self.len())) == value"]
    #[ensures="forall i: usize :: (0 <= i && i < old(self.len())) ==>
                    self.lookup(i) == old(self.lookup(i))"]
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
    #[requires="self.is_some()"]
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

// Adapted from https://doc.rust-lang.org/src/core/cmp.rs.html#962-966
#[ensures="*a == old(*a)"]
#[ensures="*b == old(*b)"]
#[ensures="(match result {
                Equal => *a == *b,
                Less => *a < *b,
                Greater => *a > *b,
            })"]
fn cmp(a: &mut i32, b: &mut i32) -> Ordering {
    if *a == *b { Equal }
    else if *a < *b { Less }
    else { Greater }
}

#[requires="forall k1: usize, k2: usize :: (0 <= k1 && k1 < k2 && k2 < arr.len()) ==>
             arr.lookup(k1) <= arr.lookup(k2)"]
#[ensures="arr.len() == old(arr.len())"]
#[ensures="forall k: usize:: (0 <= k && k < arr.len()) ==> arr.lookup(k) == old(arr.lookup(k))"]
#[ensures="*elem == old(*elem)"]
fn binary_search(arr: &mut VecWrapperI32, elem: &mut i32) -> UsizeOption
{
    let mut size = arr.len();
    let mut base = 0;

    let mut result = UsizeOption::None;
    let mut continue_loop = size > 0;

    #[invariant="0 <= base"]
    #[invariant="0 <= size"]
    #[invariant="base < 18446744073709551615 - size"]
    #[invariant="base + size <= arr.len()"]
    #[invariant="continue_loop ==> size > 0"]
    #[invariant="arr.len() == old(arr.len())"]
    #[invariant="*elem == old(*elem)"]
    #[invariant="forall k1: usize, k2: usize :: (0 <= k1 && k1 < k2 && k2 < arr.len()) ==>
                arr.lookup(k1) <= arr.lookup(k2)"]
    #[invariant="forall k: usize:: (0 <= k && k < arr.len()) ==> arr.lookup(k) == old(arr.lookup(k))"]
    #[invariant="forall k: usize:: (0 <= k && k < base) ==> arr.lookup(k) < *elem"]
    // TODO: Finish
    //#[invariant="continue_loop ==>
                 //(forall k: usize:: (base + size < k && k < arr.len()) ==> *elem < arr.lookup(k))"]
    while continue_loop {
        size /= 2;
        let mid = base + size;

        let mid_element = arr.borrow(mid);
        let cmp_result = cmp(mid_element, elem);
        base = match cmp_result {
            Less    => mid,
            Greater => base,
            Equal   => {
                result = UsizeOption::Some(mid);
                base   // Just return anything because we are finished.
            }
        };
        continue_loop = size > 0 && result.is_none();
    }

    result
}

fn main() {}
