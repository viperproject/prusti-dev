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
    pub fn index(&self, index: usize) -> &i32 {
        &self.v[index]
    }

    #[trusted]
    #[requires="0 <= index && index < self.len()"]
    #[ensures="*result == old(self.lookup(index))"]
    #[ensures="after_expiry(
        self.len() == old(self.len()) &&
        self.lookup(index) == before_expiry(*result) &&
        forall i: usize :: (0 <= i && i < self.len() && i != index) ==>
                    self.lookup(i) == old(self.lookup(i))
        )"]
    pub fn index_mut(&mut self, index: usize) -> &mut i32 {
        &mut self.v[index]
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

#[ensures="array.len() == old(array.len())"]
#[ensures="forall k1: usize, k2: usize :: (0 <= k1 && k1 < k2 && k2 < array.len()) ==>
             array.lookup(k1) <= array.lookup(k2)"]
fn selection_sort(mut array: &mut VecWrapperI32) {
 
    let mut min;
 
    let mut i = 0;
    let mut continue_loop_1 = i < array.len();
    #[invariant="array.len() == old(array.len())"]
    #[invariant="0 <= i && i < array.len()"]
    #[invariant="continue_loop_1 ==> i < array.len()"]
    #[invariant="!continue_loop_1 ==> i == array.len()"]
    #[invariant="forall k1: usize, k2: usize :: (0 <= k1 && k1 < k2 && k2 < i) ==>
                 array.lookup(k1) <= array.lookup(k2)"]
    #[invariant="forall k1: usize, k2: usize :: (0 <= k1 && k1 < i && i <= k2 && k2 < array.len()) ==>
                 array.lookup(k1) <= array.lookup(k2)"]
    while continue_loop_1 {
        min = i;

        let mut j = i+1;
        let mut continue_loop_2 = j < array.len();
        #[invariant="array.len() == old(array.len())"]
        #[invariant="0 <= i && i < array.len()"]
        #[invariant="forall k1: usize, k2: usize :: (0 <= k1 && k1 < k2 && k2 < i) ==>
                     array.lookup(k1) <= array.lookup(k2)"]
        #[invariant="forall k1: usize, k2: usize :: (0 <= k1 && k1 < i && i <= k2 && k2 < array.len()) ==>
                     array.lookup(k1) <= array.lookup(k2)"]

        #[invariant="i < j"]
        #[invariant="j < array.len()"]
        #[invariant="i <= min"]
        #[invariant="min < array.len()"]
        #[invariant="forall k1: usize :: (0 <= k1 && k1 < i) ==>
                     array.lookup(k1) <= array.lookup(min)"]
        #[invariant="forall k: usize ::
                     (i <= k && k < j && k < array.len()) ==>
                     array.lookup(min) <= array.lookup(k)"]
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

#[trusted]
fn print_initial_array(array: &mut VecWrapperI32) {
    println!("The initial array is {:?}", array.v);
}

#[trusted]
#[requires="forall k1: usize, k2: usize :: (0 <= k1 && k1 < k2 && k2 < array.len()) ==>
             array.lookup(k1) <= array.lookup(k2)"]
fn print_sorted_array(array: &mut VecWrapperI32) {
    println!(" The sorted array is {:?}", array.v);
}
 
pub fn test() {
    let mut array = VecWrapperI32::new();
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
