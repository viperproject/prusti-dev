use prusti_contracts::*;

use std::cmp::{Ord, Ordering};

#[extern_spec]
trait Ord {
    #[pure]
    fn cmp(&self, other: &Self) -> Ordering;
}

#[extern_spec]
impl Ord for i32 {
    #[ensures(match result {
        Ordering::Less => *self < *other,
        Ordering::Greater => *self > *other,
        Ordering::Equal => *self == *other,
    })]
    #[pure]
    pub fn cmp(&self, other: &Self) -> Ordering;
}

#[requires(match x.cmp(&y) {
    Ordering::Less => false,
    Ordering::Greater => false,
    Ordering::Equal => true,
})]
fn foo(x: i32, y: i32) {}

fn main() {
    foo(3, 3);
}
