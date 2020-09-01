//! An adaptation of the example from
//! https://rosettacode.org/wiki/Sorting_algorithms/Selection_sort#Rust
//!
//! Changes:
//!
//! +   Wrapped built-in types and functions.
//! +   Rewrote loops into supported shape (while bool with no break, continue, or return).
//! +   Replaced ``println!`` with calling trusted functions.
//!
//! Verified properties:
//!
//! +   Absence of panics.
//! +   Absence of overflows.
//! +   The resulting vector is sorted.

extern crate prusti_contracts;

pub struct VecWrapper<T>{
    v: Vec<T>
}

impl<T> VecWrapper<T> {

    #[trusted]
    #[ensures="result.len() == 0"]
    pub fn new() -> Self {
        VecWrapper{ v: Vec::new() }
    }

    #[trusted]
    #[ensures="self.len() == old(self.len()) + 1"]
    pub fn push(&mut self, value: T) {
        self.v.push(value);
    }

    #[trusted]
    #[pure]
    pub fn len(&self) -> usize {
        self.v.len()
    }

    #[trusted]
    #[requires="0 <= index && index < self.len()"]
    pub fn index(&self, index: usize) -> &T {
        &self.v[index]
    }

    #[trusted]
    #[requires="0 <= index && index < self.len()"]
    #[ensures="after_expiry(self.len() == old(self.len()))"]
    pub fn index_mut(&mut self, index: usize) -> &mut T {
        &mut self.v[index]
    }
}

#[ensures="array.len() == old(array.len())"]
fn selection_sort(mut array: &mut VecWrapper<i32>) {

    let mut min;

    let mut i = 0;
    let mut continue_loop_1 = i < array.len();
    #[invariant="i < array.len()"]
    #[invariant="array.len() == old(array.len())"]
    #[invariant="0 <= i && i <= array.len()"]
    #[invariant="continue_loop_1 ==> i < array.len()"]
    while continue_loop_1 {
        min = i;

        let mut j = i+1;
        let mut continue_loop_2 = j < array.len();
        #[invariant="j < array.len()"]
        #[invariant="array.len() == old(array.len())"]
        #[invariant="0 < j && j <= array.len()"]
        #[invariant="continue_loop_2 ==> j < array.len()"]
        #[invariant="0 <= min && min < array.len()"]
        while continue_loop_2 {
            if *array.index(j) < *array.index(min) {
                min = j;
            }
            j += 1;
            continue_loop_2 = j < array.len();
        }

        let tmp = *array.index(i);
        let min_value = *array.index(min);
        let p = array.index_mut(i);
        *p = min_value;
        let p = array.index_mut(min);
        *p = tmp;

        i += 1;

        continue_loop_1 = i < array.len();
    }

}

use std::fmt::Debug;

#[trusted]
fn print_initial_array<T: Debug>(array: &mut VecWrapper<T>) {
    println!("The initial array is {:?}", array.v);
}

#[trusted]
fn print_sorted_array<T: Debug>(array: &mut VecWrapper<T>) {
    println!(" The sorted array is {:?}", array.v);
}

pub fn test() {
    let mut array = VecWrapper::new();
    array.push(9);
    array.push(4);
    array.push(8);
    array.push(3);
    array.push(-6);
    array.push(2);
    array.push(1);
    array.push(6);

    print_initial_array(&mut array);

    selection_sort(&mut array);

    print_sorted_array(&mut array);
}

fn main() { }
