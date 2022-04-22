use prusti_contracts::*;
use std::cmp::{Ord, Ordering};
fn main() {}

#[extern_spec]
trait Ord {
    #[pure]
    fn cmp(&self, other: &Self) -> Ordering;
}

#[pure]
pub fn eq<T: Ord>(a: &T, b: &T) -> bool {
    match a.cmp(b) {
        Ordering::Equal => true,
        Ordering::Less => false,
        Ordering::Greater => false,
    }
}
