//! An adaptation of the example from
//! https://rosettacode.org/wiki/Sorting_algorithms/Heapsort#Rust
//!
//! Changes:
//!
//! +   Monomorphised types.
//! +   Wrapped built-in types and functions.
//! +   Replaced closure with a function.
//! +   Rewrote loops into supported shape (while bool with no break, continue, or return).
//!
//! Verified properties:
//!
//! +   Absence of panics.

extern crate prusti_contracts;

pub struct VecWrapperI32{
    v: Vec<i32>
}

impl VecWrapperI32 {

    #[trusted]
    #[pure]
    #[ensures="result >= 0"]
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
    #[requires="0 <= index && index < self.len()"]
    #[ensures="self.len() == old(self.len())"]
    #[ensures="self.lookup(index) == value"]
    #[ensures="forall i: usize :: (0 <= i && i < self.len() && i != index) ==>
                    self.lookup(i) == old(self.lookup(i))"]
    pub fn store(&mut self, index: usize, value: i32) {
        self.v[index] = value;
    }

    #[trusted]
    #[ensures="self.len() == old(self.len()) + 1"]
    #[ensures="self.lookup(old(self.len())) == value"]
    #[ensures="forall i: usize :: (0 <= i && i < old(self.len())) ==>
                    self.lookup(i) == old(self.lookup(i))"]
    pub fn push(&mut self, value: i32) {
        self.v.push(value);
    }

    #[trusted]
    #[requires="0 <= index_a && index_a < self.len()"]
    #[requires="0 <= index_b && index_b < self.len()"]
    #[ensures="self.len() == old(self.len())"]
    #[ensures="self.lookup(index_a) == old(self.lookup(index_b))"]
    #[ensures="self.lookup(index_b) == old(self.lookup(index_a))"]
    #[ensures="forall i: usize :: (0 <= i && i < self.len() && i != index_a && i != index_b) ==>
                    self.lookup(i) == old(self.lookup(i))"]
    pub fn swap(&mut self, index_a: usize, index_b: usize) {
        self.v.swap(index_a, index_b);
    }
}

#[pure]
fn order(x: i32, y: i32) -> bool {
    x < y
}

fn main() {
    /*let mut v = VecWrapperI32::new();
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
    heap_sort(&mut v);*/
}

#[ensures="array.len() == old(array.len())"]
fn heap_sort(array: &mut VecWrapperI32)
{
    let len = array.len();

    let mut start = len/2;
    let mut continue_loop = start > 0;
    // Create heap
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
    #[invariant="len == array.len()"]
    #[invariant="end <= len"]
    #[invariant="end > 1"]
    while continue_loop {
        end -= 1;
        let start = 0;
        array.swap(start, end);
        shift_down(array, start, end - 1);
        continue_loop = end > 1;
    }
}

#[requires="end < array.len()"]
#[requires="0 <= start && start < array.len()"]
#[requires="0 <= end && end < array.len()"]
#[ensures="array.len() == old(array.len())"]
fn shift_down(array: &mut VecWrapperI32, start: usize, end: usize)
{
    let mut root = start;
    let mut continue_loop = true;
    #[invariant="0 <= root && root < array.len()"]
    #[invariant="0 <= end && end < array.len()"]
    #[invariant="array.len() == old(array.len())"]
    while continue_loop {
        let mut child = root * 2 + 1;
        if child > end {
            continue_loop = false;
        } else {
            if child + 1 <= end && order(*array.borrow(child), *array.borrow(child + 1)) {
                child += 1;
            }
            if order(*array.borrow(root), *array.borrow(child)) {
                array.swap(root, child);
                root = child
            } else {
                continue_loop = false;
            }
        }
    }
}
