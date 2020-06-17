//! An adaptation of the example from
//! https://rosettacode.org/wiki/Sorting_algorithms/Heapsort#Rust
//!
//! Changes:
//!
//! +   Wrapped built-in types and functions.
//! +   Replaced closure with a function.
//! +   Replaced a slice with a reference into a vector.
//! +   Rewrote loops into supported shape (while bool with no break, continue, or return).
//!
//! Verified properties:
//!
//! +   Absence of panics.

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

    #[trusted]
    #[requires="0 <= index_a && index_a < self.len()"]
    #[requires="0 <= index_b && index_b < self.len()"]
    #[ensures="self.len() == old(self.len())"]
    pub fn swap(&mut self, index_a: usize, index_b: usize) {
        self.v.swap(index_a, index_b);
    }
}

#[trusted]
#[pure]
fn order<T>(_x: &T, _y: &T) -> bool {
    unimplemented!()
}

#[requires="array.len() < std::usize::MAX/2"]
#[ensures="array.len() == old(array.len())"]
fn heap_sort<T>(array: &mut VecWrapper<T>)
{
    let len = array.len();

    let mut start = len/2;
    let mut continue_loop = start > 0;
    // Create heap
    #[invariant="array.len() < std::usize::MAX/2"]
    #[invariant="len == array.len()"]
    #[invariant="start <= len/2"]
    #[invariant="start > 0"]
    while continue_loop {
        start -= 1;
        shift_down(array, start, len - 1);
        continue_loop = start > 0;
    }

    let mut end = len;
    let mut continue_loop = end > 1;
    #[invariant="array.len() < std::usize::MAX/2"]
    #[invariant="len == array.len()"]
    #[invariant="end <= len"]
    #[invariant="end > 1"]
    while continue_loop {
        end -= 1;
        let zero = 0;
        array.swap(zero, end);
        shift_down(array, zero, end - 1);
        continue_loop = end > 1;
    }
}

#[requires="array.len() < std::usize::MAX/2"]
#[requires="0 <= start && start < array.len()/2"]
#[requires="0 <= end && end < array.len()"]
#[ensures="array.len() == old(array.len())"]
fn shift_down<T>(array: &mut VecWrapper<T>, start: usize, end: usize) {
    let mut root = start;
    let mut continue_loop = true;
    #[invariant="array.len() < std::usize::MAX/2"]
    #[invariant="0 <= root && root < array.len()"]
    #[invariant="0 <= end && end < array.len()"]
    #[invariant="array.len() == old(array.len())"]
    while continue_loop {
        let mut child = root * 2 + 1;
        if child > end {
            continue_loop = false;
        } else {
            if child + 1 <= end && order(array.index(child), array.index(child + 1)) {
                child += 1;
            }
            if order(array.index(root), array.index(child)) {
                array.swap(root, child);
                root = child
            } else {
                continue_loop = false;
            }
        }
    }
}

pub fn test() {
    let mut v = VecWrapper::<i32>::new();
    v.push(4);
    v.push(6);
    v.push(8);
    v.push(1);
    v.push(0);
    v.push(3);
    v.push(2);
    v.push(2);
    v.push(9);
    v.push(5);
    assert!(v.len() == 10);
    heap_sort(&mut v);
}

fn main() {}
