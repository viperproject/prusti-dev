use prusti_contracts::*;
use std::cmp::Ordering;

#[pure]
fn cmp(x: i32, y: i32) -> Ordering {
    Ordering::Less
}

fn main() {}
