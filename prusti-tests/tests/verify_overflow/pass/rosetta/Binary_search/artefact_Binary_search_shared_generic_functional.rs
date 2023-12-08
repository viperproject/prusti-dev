// compile-flags: -Puse_more_complete_exhale=false

//! A copy of `artefact_Binary_search_shared.rs` with fixed non-termination bug and manually
//! encoded termination check.

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
    #[ensures(result === self.lookup(index))]
    pub fn index(&self, index: usize) -> &T {
        &self.v[index]
    }

    #[pure]
    #[trusted]
    #[requires(0 <= index && index < self.len())]
    pub fn lookup(&self, index: usize) -> &T {
        &self.v[index]
    }
}

pub enum MyOption<T> {
    Some(T),
    None,
}

impl<T> MyOption<T> {
    #[pure]
    pub fn is_some(&self) -> bool {
        match self {
            MyOption::Some(_) => true,
            MyOption::None => false,
        }
    }
    #[pure]
    pub fn is_none(&self) -> bool {
        match self {
            MyOption::Some(_) => false,
            MyOption::None => true,
        }
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
#[requires(cmp(bound, elem) === Less)]
#[ensures(
    forall(|a: &T|
        matches!(cmp(a, bound), Less | Equal) ==>
        cmp(a, elem) === Less,
        triggers=[(cmp(a, elem),)])
)]
fn lemma_cmp_less_transitive<T: Ord>(bound: &T, elem: &T) {}

#[trusted]
#[requires(cmp(bound, elem) === Greater)]
#[ensures(
    forall(|a: &T|
        matches!(cmp(bound, a), Less | Equal) ==>
        cmp(a, elem) === Greater,
        triggers=[(cmp(a, elem),)])
)]
fn lemma_cmp_greater_transitive<T: Ord>(bound: &T, elem: &T) {}

#[requires(forall(|k1: usize, k2: usize| (0 <= k1 && k1 < k2 && k2 < arr.len()) ==>
             matches!(cmp(arr.lookup(k1), arr.lookup(k2)), Less | Equal)))]
#[ensures(result.is_none() ==>
            (forall(|k: usize| (0 <= k && k < arr.len()) ==> elem !== arr.lookup(k))))]
#[ensures(match result {
                MyOption::Some(index) => (
                    0 <= index && index < arr.len() &&
                    arr.lookup(index) === elem
                ),
                MyOption::None => true,
            })]
fn binary_search<T: Ord>(arr: &VecWrapper<T>, elem: &T) -> MyOption<usize> {
    let mut size = arr.len();
    let mut base = 0;

    let mut result = MyOption::None;
    let mut continue_loop = size > 0;


    while continue_loop {
        body_invariant!(continue_loop == (size > 0 && result.is_none()));
        body_invariant!(base + size <= arr.len());
        body_invariant!(forall(|k: usize| (0 <= k && k < base) ==>
            cmp(arr.lookup(k), elem) === Less, triggers=[(arr.lookup(k),),]));
        body_invariant!(result.is_none() ==>
                (forall(|k: usize| (base + size <= k && k < arr.len()) ==>
                        cmp(arr.lookup(k), elem) === Greater, triggers=[(arr.lookup(k),),])));
        body_invariant!(match result {
                    MyOption::Some(index) => (
                        0 <= index && index < arr.len() &&
                        arr.lookup(index) === elem
                    ),
                    MyOption::None => true,
                });
        let ghost_old_size = size;

        let half = size / 2;
        let mid = base + half;

        let mid_element = arr.index(mid);
        let cmp_result = cmp(mid_element, elem);
        base = match cmp_result {
            Less    => {
                lemma_cmp_less_transitive(mid_element, elem);
                mid
            },
            Greater => {
                lemma_cmp_greater_transitive(mid_element, elem);
                base
            },
            // Equal
            _   => {
                result = MyOption::Some(mid);
                base   // Just return anything because we are finished.
            }
        };

        if half == 0 {
            break;
        }

        size -= half;
        continue_loop = size > 0 && result.is_none();

        prusti_assert!(ghost_old_size >= 0 && ghost_old_size > size);   // Termination check.
    }

    result
}

fn main() {}

