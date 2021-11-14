//! This file tests that the programs compile when NOT built by Prusti.

use prusti_contracts::*;

#[requires(true)]
fn test1() {}

#[ensures(true)]
fn test2() {}

fn test3() {
    for _ in 0..2 {
        body_invariant!(true);
    }
}

#[requires(true)]
#[ensures(true)]
fn test4() {
    for _ in 0..2 {
        body_invariant!(true);
    }
}

#[pure]
#[trusted]
fn test5() {}

predicate! {
    fn pred_ok() -> bool {
        true
    }
}

fn test_closures() {
    let cl1 = closure!(
        requires(true),
        ensures(true),
        || -> usize { 1 }
    );
    assert_eq!(1usize, cl1());

    let cl2 = closure!(
        requires(true),
        || -> usize { 1 }
    );
    assert_eq!(1usize, cl2());

    let cl3 = closure!(
        ensures(true),
        || -> usize { 1 }
    );
    assert_eq!(1usize, cl3());

    let cl4 = closure!(
        || -> usize { 1 }
    );
    assert_eq!(1usize, cl4());

    let cl5 = closure!(|| -> () {});
    assert_eq!((), cl5());
}

fn main() {}
