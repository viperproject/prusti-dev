use prusti_contracts::*;
use std::cmp::{Ord, Ordering};

#[extern_spec]
trait Ord {
    #[pure]
    fn cmp(&self, other: &Self) -> Ordering;
}

#[pure]
fn compare<T: Ord>(a: &T, other: &T) -> Ordering {
    a.cmp(other)
}

fn main() {}
