// compile-flags: -Puse_more_complete_exhale=false

//! An adaptation of the example from
//! https://rosettacode.org/wiki/Binary_search#Rust
//!
//! The original example:
//! ```rust
//! use std::cmp::Ordering::*;
//! fn binary_search<T: Ord>(arr: &[T], elem: &T) -> Option<usize>
//! {
//!     let mut size = arr.len();
//!     let mut base = 0;
//!
//!     while size > 0 {
//!         size /= 2;
//!         let mid = base + size;
//!         base = match arr[mid].cmp(elem) {
//!             Less    => mid,
//!             Greater => base,
//!             Equal   => return Some(mid)
//!         };
//!     }
//!
//!     None
//! }
//! ```
//!
//! Changes:
//!
//! +   Wrapped built-in types and functions.
//! +   Add additional functions for capturing functional specification.
//! +   Replaced a slice with a reference into a vector.
//! +   Changed the loop into the supported shape.
//! +   Removed the return statement.
//! +   Monomorphised types.
//!
//! Verified properties:
//!
//! +   Absence of panics.
//! +   Absence of overflows.
//! +   If the result is `None`, then the input vector did not contain the
//!     element.
//! +   If the result is `Some(index)` then the `arr[index] == elem`.
//!
//! The original example contains a bug, which can be showed by using
//! the following counter-example:
//!
//! ```rust
//! fn main() {
//!     let v = vec![0, 1, 2, 3, 4, 5, 6];
//!     println!("{:?}", binary_search(&v, &6));
//! }
//! ```
//!
//! This program should print `Some(6)`, but it prints None. The fixed
//! version would be:
//!
//! ```rust
//! use std::cmp::Ordering::*;
//! fn binary_search<T: Ord>(arr: &[T], elem: &T) -> Option<usize>
//! {
//!     let mut size = arr.len();
//!     let mut base = 0;
//!
//!     while size > 0 {
//!         let half = size / 2;
//!         let mid = base + half;
//!         base = match arr[mid].cmp(elem) {
//!             Less    => mid,
//!             Greater => base,
//!             Equal   => return Some(mid)
//!         };
//!         size -= half;
//!     }
//!
//!     None
//! }
//! ```
//!
//! This file contains a verified version of it.

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
    #[pure]
    #[requires(0 <= index && index < self.len())]
    pub fn lookup(&self, index: usize) -> i32 {
        self.v[index]
    }

    #[trusted]
    #[requires(0 <= index && index < self.len())]
    #[ensures(self.lookup(index) == *result)]
    pub fn index(&self, index: usize) -> &i32 {
        &self.v[index]
    }
}

pub enum UsizeOption {
    Some(usize),
    None,
}

impl UsizeOption {
    #[pure]
    pub fn is_some(&self) -> bool {
        match self {
            UsizeOption::Some(_) => true,
            UsizeOption::None => false,
        }
    }
    #[pure]
    pub fn is_none(&self) -> bool {
        match self {
            UsizeOption::Some(_) => false,
            UsizeOption::None => true,
        }
    }
}

pub enum Ordering {
    Less,
    Equal,
    Greater,
}

use self::Ordering::*;

#[ensures(match result {
                Equal => *a == *b,
                Less => *a < *b,
                Greater => *a > *b,
            })]
fn cmp(a: &i32, b: &i32) -> Ordering {
    if *a == *b { Equal }
        else if *a < *b { Less }
            else { Greater }
}


#[requires(forall(|k1: usize, k2: usize| (0 <= k1 && k1 < k2 && k2 < arr.len()) ==>
             arr.lookup(k1) <= arr.lookup(k2)))]
#[ensures(result.is_none() ==>
            (forall(|k: usize| (0 <= k && k < arr.len()) ==> *elem != arr.lookup(k))))]
#[ensures(match result {
                UsizeOption::Some(index) => (
                    0 <= index && index < arr.len() &&
                    arr.lookup(index) == *elem
                ),
                UsizeOption::None => true,
            })]
fn binary_search(arr: &VecWrapperI32, elem: &i32) -> UsizeOption {
    let mut size = arr.len();
    let mut base = 0;

    let mut result = UsizeOption::None;
    let mut continue_loop = size > 0;


    while continue_loop {
        body_invariant!(continue_loop == (size > 0 && result.is_none()));
        body_invariant!(base + size <= arr.len());
        body_invariant!(forall(|k1: usize, k2: usize| (0 <= k1 && k1 < k2 && k2 < arr.len()) ==>
            arr.lookup(k1) <= arr.lookup(k2)));
        body_invariant!(forall(|k: usize| (0 <= k && k < base) ==> arr.lookup(k) < *elem));
        body_invariant!(result.is_none() ==>
                (forall(|k: usize| (base + size <= k && k < arr.len()) ==> *elem != arr.lookup(k))));
        body_invariant!(match result {
                    UsizeOption::Some(index) => (
                        0 <= index && index < arr.len() &&
                        arr.lookup(index) == *elem
                    ),
                    UsizeOption::None => true,
                });
        let half = size / 2;
        let mid = base + half;

        let mid_element = arr.index(mid);
        let cmp_result = cmp(mid_element, elem);
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
