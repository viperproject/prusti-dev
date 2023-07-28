//! This file tests that the programs compile when NOT built by Prusti.
#![allow(dead_code)]

// These feature flags are not needed when executing under Prusti
// because it generates them for us.
#![cfg_attr(feature = "prusti", feature(register_tool))]
#![cfg_attr(feature = "prusti", register_tool(prusti))]

use prusti_contracts::*;

#[extern_spec]
#[allow(unused_must_use)]
impl<T> std::option::Option<T> {
    #[pure]
    #[ensures(matches!(*self, Some(_)) == result)]
    pub fn is_some(&self) -> bool;

    #[pure]
    #[ensures(self.is_some() == !result)]
    pub fn is_none(&self) -> bool;

    #[requires(self.is_some())]
    pub fn unwrap(self) -> T;
}

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
        #[requires(true)]
        #[ensures(true)]
        || -> usize { 1 }
    );
    assert_eq!(1usize, cl1());

    let cl2 = closure!(
        #[requires(true)]
        || -> usize { 1 }
    );
    assert_eq!(1usize, cl2());

    let cl3 = closure!(
        #[ensures(true)]
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
