//! An monomorphised version from
//! https://rosettacode.org/mw/index.php?title=Binary_search&oldid=278774#Rust
//! that contains a bug.

use prusti_contracts::*;

use std::cmp::Ordering::{self, *};

#[extern_spec]
impl i32 {
    #[ensures(
        match result {
            Less => *self < *other,
            Greater => *self > *other,
            Equal => *self == *other,
        }
    )]
    pub fn cmp(&self, other: &i32) -> Ordering;
}

predicate! {
    fn sorted(s: &[i32]) -> bool {
        forall(|i: usize, j: usize| (i < j && j < s.len()) ==> s[i] <= s[j])
    }
}

predicate! {
    fn contains_not(s: &[i32], start: usize, end: usize, n: i32) -> bool {
        forall(|i: usize| (start <= i && i < end) ==> s[i] != n)
    }
}

fn binary_search_iterative1_no_spec(arr: &[i32], elem: i32) -> Option<usize>
{
    let mut size = arr.len();
    let mut base = 0;
 
    while size > 0 {
        body_invariant!(base + size <= arr.len());
        size /= 2;
        let mid = base + size;
        base = match arr[mid].cmp(&elem) {
            Less    => mid,
            Greater => base,
            Equal   => return Some(mid)
        };
    }
 
    None
}

#[requires(sorted(arr))]
#[ensures(
    match result {
        Some(index) => index < arr.len() && arr[index] == elem,
        None => contains_not(arr, 0, arr.len(), elem),
    }
)]
fn binary_search_iterative1_with_spec(arr: &[i32], elem: i32) -> Option<usize>
{
    let mut size = arr.len();
    let mut base = 0;
 
    while size > 0 {
        body_invariant!(base + size <= arr.len());
        body_invariant!(sorted(arr));
        body_invariant!(elem == old(elem));
        body_invariant!(size > 0);
        body_invariant!(forall(|k: usize| (k < base) ==> arr[k] < elem));
        body_invariant!(contains_not(arr, base + size, arr.len(), elem)); //~ ERROR: loop invariant might not hold after a loop iteration that preserves the loop condition.
        size /= 2;
        let mid = base + size;
        base = match arr[mid].cmp(&elem) {
            Less    => mid,
            Greater => base,
            Equal   => return Some(mid)
        };
    }
 
    None
}

#[requires(sorted(arr))]
#[ensures(
    match result {
        Some(index) => index < arr.len() && arr[index] == elem,
        None => contains_not(arr, 0, arr.len(), elem),
    }
)]
fn binary_search_iterative1_fixed(arr: &[i32], elem: i32) -> Option<usize>
{
    let mut size = arr.len();
    let mut base = 0;
 
    while size > 0 {
        body_invariant!(base + size <= arr.len());
        body_invariant!(sorted(arr));
        body_invariant!(elem == old(elem));
        body_invariant!(size > 0);
        body_invariant!(forall(|k: usize| (k < base) ==> arr[k] < elem));
        body_invariant!(contains_not(arr, base + size, arr.len(), elem));
        let half = size / 2;
        let mid = base + half;
        base = match arr[mid].cmp(&elem) {
            Less    => mid,
            Greater => base,
            Equal   => return Some(mid)
        };
        size -= half;
    }
 
    None
}

pub fn binary_search(data: &[i32], target: i32) -> Option<usize> {
    let mut high = data.len();
    let mut low = 0;
    let mut mid = high / 2;
 
    while low < high {
        let _result = match target.cmp(&data[mid]) {
            Less => {
                high = mid;
            },
            Greater => {
                low = mid;
            },
            Equal => return Some(mid)
        };
        mid = (high + low) / 2; //~ ERROR: assertion might fail with "attempt to add with overflow"
    }
    None
}

fn main() {}
