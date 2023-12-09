// compile-flags: -Puse_more_complete_exhale=false

//! An adaptation of the example from
//! https://rosettacode.org/wiki/Sorting_algorithms/Selection_sort#Rust
//!
//! Changes:
//!
//! +   Wrapped built-in types and functions.
//! +   Rewrote loops into supported shape (while bool with no break, continue, or return).
//! +   Replaced ``println!`` with calling trusted functions.
//! +   Made generic over `T`.
//!
//! Verified properties:
//!
//! +   Absence of panics.
//! +   Absence of overflows.
//! +   The resulting vector is sorted.

use prusti_contracts::*;

pub struct VecWrapper<T>{
    v: Vec<T>
}

impl<T> VecWrapper<T> {

    #[trusted]
    #[ensures(result.len() == 0)]
    pub fn new() -> Self {
        VecWrapper{ v: Vec::new() }
    }

    #[trusted]
    #[ensures(self.len() == old(self.len()) + 1)]
    pub fn push(&mut self, value: T) {
        self.v.push(value);
    }

    #[trusted]
    #[pure]
    pub fn len(&self) -> usize {
        self.v.len()
    }

    #[trusted]
    #[pure]
    #[requires(0 <= index && index < self.len())]
    pub fn lookup(&self, index: usize) -> &T {
        &self.v[index]
    }

    #[trusted]
    #[requires(0 <= index && index < self.len())]
    #[ensures(result === old(self.lookup(index)))]
    pub fn index(&self, index: usize) -> &T {
        &self.v[index]
    }

    #[trusted]
    #[requires(0 <= index && index < self.len())]
    #[ensures(&*result === old(self.lookup(index)))]
    #[after_expiry(
        self.len() == old(self.len()) &&
        self.lookup(index) === before_expiry(result) &&
        forall(|i: usize| (0 <= i && i < self.len() && i != index) ==>
                    self.lookup(i) === old(self.lookup(i)))
    )]
    pub fn index_mut(&mut self, index: usize) -> &mut T {
        &mut self.v[index]
    }

    #[trusted]
    #[requires(0 <= a && a < self.len())]
    #[requires(0 <= b && b < self.len())]
    #[ensures(self.len() == old(self.len()))]
    #[ensures(self.lookup(a) === old(self.lookup(b)))]
    #[ensures(self.lookup(b) === old(self.lookup(a)))]
    #[ensures(
        forall(|i: usize| (0 <= i && i < self.len() && i != a && i != b) ==>
                    self.lookup(i) === old(self.lookup(i)))
    )]
    pub fn swap(&mut self, a: usize, b: usize) {
        self.v.swap(a, b);
    }
}

#[derive(Clone, Copy)]
pub enum Ordering {
    Less,
    Equal,
    Greater,
}

use self::Ordering::*;

#[trusted]
#[pure]
#[ensures(matches!(result, Equal) == (a === b))]
fn cmp<T: Ord>(a: &T, b: &T) -> Ordering {
    match Ord::cmp(a, b) {
        std::cmp::Ordering::Less => Less,
        std::cmp::Ordering::Equal => Equal,
        std::cmp::Ordering::Greater => Greater,
    }
}

#[trusted]
#[requires(cmp(elem, bound) === Less)]
#[ensures(forall(|a: &T| matches!(cmp(bound, a), Less | Equal) ==>
    matches!(cmp(elem, a), Less | Equal),
    triggers=[(cmp(elem, a),)]
))]
fn lemma_cmp_less_transitive<T: Ord>(bound: &T, elem: &T) {}

/*
#[requires(0 <= bound && bound < array.len())]
#[requires(0 <= elem && elem < array.len())]
#[requires(cmp(array.lookup(elem), array.lookup(bound)) === Less)]
#[ensures(forall(|a: &T| matches!(cmp(array.lookup(bound), a), Less | Equal) ==>
    matches!(cmp(array.lookup(elem), a), Less | Equal),
    triggers=[(cmp(array.lookup(elem), a),)]
))]
fn lemma_cmp_less_transitive_array<T: Ord>(array: &VecWrapper<T>, bound: usize, elem: usize) {
    lemma_cmp_less_transitive(array.index(bound), array.index(elem));
}
*/

#[trusted]
#[requires(cmp(a, b) !== Less)]
#[ensures(matches!(cmp(b, a), Less | Equal))]
fn lemma_cmp_not_less<T: Ord>(a: &T, b: &T) {}

macro_rules! smaller_equals {
    ($array:expr, $k1:expr, $k2:expr) => {
        matches!(cmp($array.lookup($k1), $array.lookup($k2)), Less | Equal)
    };
}

#[ensures(array.len() == old(array.len()))]
#[ensures(forall(|k1: usize, k2: usize| (0 <= k1 && k1 < k2 && k2 < array.len()) ==>
             smaller_equals!(array, k1, k2)))]
fn selection_sort<T: Ord>(mut array: &mut VecWrapper<T>) {

    let mut min;

    let mut i = 0;
    let mut continue_loop_1 = i < array.len();
    while continue_loop_1 {
        body_invariant!(array.len() == old(array.len()));
        body_invariant!(0 <= i && i <= array.len());
        body_invariant!(continue_loop_1 ==> i < array.len());
        body_invariant!(!continue_loop_1 ==> i == array.len());
        body_invariant!(forall(|k1: usize, k2: usize| (0 <= k1 && k1 < k2 && k2 < i) ==>
                 smaller_equals!(array, k1, k2)));
        body_invariant!(forall(|k1: usize, k2: usize| (0 <= k1 && k1 < i && i <= k2 && k2 < array.len()) ==>
                 smaller_equals!(array, k1, k2)));
        min = i;

        let mut j = i+1;
        let mut continue_loop_2 = j < array.len();
        while continue_loop_2 {
            body_invariant!(array.len() == old(array.len()));
            body_invariant!(0 <= i && i < array.len());
            body_invariant!(forall(|k1: usize, k2: usize| (0 <= k1 && k1 < k2 && k2 < i) ==>
                     smaller_equals!(array, k1, k2)));
            body_invariant!(forall(|k1: usize, k2: usize| (0 <= k1 && k1 < i && i <= k2 && k2 < array.len()) ==>
                     smaller_equals!(array, k1, k2)));

            body_invariant!(i < j);
            body_invariant!(j < array.len());
            body_invariant!(i <= min);
            body_invariant!(min < array.len());
            body_invariant!(forall(|k1: usize| (0 <= k1 && k1 < i) ==>
                    smaller_equals!(array, k1, min)));
            body_invariant!(forall(|k: usize|
                     (i <= k && k < j && k < array.len()) ==>
                     smaller_equals!(array, min, k)));
            let cmp_result = cmp(array.index(j), array.index(min));
            if matches!(cmp_result, Less) {
                lemma_cmp_less_transitive(array.index(min), array.index(j));
                //lemma_cmp_less_transitive_array(array, min, j);
//prusti_assume!(
//forall(|a: &T|
//cmp(array.lookup(j), array.lookup(min)) === Less &&
//matches!(cmp(array.lookup(min), a), Less | Equal) ==>
//matches!(cmp(array.lookup(j), a), Less | Equal)
       //)
    //);
                min = j;
            } else {
                lemma_cmp_not_less(array.index(j), array.index(min));
            }
            j += 1;
            continue_loop_2 = j < array.len();
        }

        array.swap(i, min);

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
