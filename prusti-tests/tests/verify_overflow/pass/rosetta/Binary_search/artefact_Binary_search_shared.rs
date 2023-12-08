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
//! +   Replaced a slice with a reference into a vector.
//! +   Change the loop into the supported shape.
//! +   Remove the return statement.
//!
//! Verified properties:
//!
//! +   Absence of panics.
//! +   Absence of overflows.
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

pub struct VecWrapper<T>{
    v: Vec<T>
}

impl<T> VecWrapper<T> {

    #[trusted]
    #[pure]
    pub fn len(&self) -> usize {
        self.v.len()
    }

    #[trusted]
    #[requires(0 <= index && index < self.len())]
    pub fn index(&self, index: usize) -> &T {
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

#[trusted]
fn cmp<T>(_a: &T, _b: &T) -> Ordering {
    unimplemented!();
}

fn binary_search<T: Ord>(arr: &VecWrapper<T>, elem: &T) -> UsizeOption {
    let mut size = arr.len();
    let mut base = 0;

    let mut result = UsizeOption::None;
    let mut continue_loop = size > 0;


    while continue_loop {
        body_invariant!(continue_loop == (size > 0 && result.is_none()));
        body_invariant!(base + size <= arr.len());
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
