// compile-flags: -Punsafe_core_proof=true
#![allow(unused)]
use prusti_contracts::*;

#[pure]
#[terminates(Int::new(x))]
#[requires(x >= 0)]
fn add_3(x: i64) -> i64 {
    if x == 0 {
        0
    } else {
        assert!(x - 1 < x && x - 1 >= 0);
        3 + add_3(x - 1)
    }
}

#[pure]
#[terminates(Int::new(x))]
#[requires(x >= 0)]
#[ensures((x % 2 == 0) == (add_3(x) % 2 == 0))]
fn lemma(x: i64) -> bool {
    if x > 0 {
        lemma(x - 1);
        if x % 2 == 0 {
            prusti_assert!((x - 1) % 2 == 1);
            prusti_assert!((add_3(x) % 2 == 0));
        } else {
            prusti_assert!(x % 2 == 1);
            prusti_assert!((x - 1) % 2 == 0);
            prusti_assert!((add_3(x) % 2 == 1));
        }
        prusti_assert!((x % 2 == 0) == (add_3(x) % 2 == 0));
    } else {
        prusti_assert!(x == 0);
        prusti_assert!(x % 2 == 0);
        prusti_assert!(add_3(x) % 2 == 0);
        prusti_assert!((x % 2 == 0) == (add_3(x) % 2 == 0));
    }
    true // FIXME: for some reason pure functions returning nothing (an empty tuple) cause a panic
}

#[requires(x >= 0)]
fn foo(x: i64) {
    let y = 2 * x;
    let z = add_3(y);
    ghost! {
        lemma(y);
    };
    assert!(z % 2 == 0);
}

fn main() {}
