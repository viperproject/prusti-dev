// compile-flags: -Puse_more_complete_exhale=false

//! A copy of `artefact_Binary_search_shared.rs` with fixed non-termination bug and manually
//! encoded termination check.

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
        let ghost_old_size = size;

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
