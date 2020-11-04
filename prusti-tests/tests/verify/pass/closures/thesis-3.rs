#![feature(stmt_expr_attributes)]

use prusti_contracts::*;

/// Examples from Fabian Wolff's thesis.

// ignore-test
// TODO: vectors, iterators, ...

fn main() {
    let nums = vec![1, 2, 3];
    // let doubled = nums.iter().map(|i| i * 2).collect::<Vec<_>>();
    let doubled = nums.iter().map(closure!(
        ensures(result == i * 2), // TODO: could this be inferred?
        |i:i32| -> i32 { i * 2 }
    )).collect::<Vec<_>>();
    assert_eq!(doubled, vec![2, 4, 6]);
}
