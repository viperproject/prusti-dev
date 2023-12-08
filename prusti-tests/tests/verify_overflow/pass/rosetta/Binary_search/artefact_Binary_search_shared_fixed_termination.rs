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
