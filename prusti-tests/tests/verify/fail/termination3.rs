// compile-flags: -Punsafe_core_proof=true

#![allow(unused)]

use prusti_contracts::*;

#[terminates]
fn main() {
    let mut x = 0;
    while x < 10 {
        //~ ERROR: this loop might not terminate
        x += 1;
    }
}

fn ghost_needs_termination() {
    ghost! {
        loop {} //~ ERROR: this loop might not terminate
    };
}

fn ghost_cant_call_impure_fn() {
    ghost! {
        main(); //~ ERROR: Only pure function calls are allowed in ghost blocks
    };
}

fn non_terminating() {}

#[terminates]
fn terminating_calls_nonterminating() {
    non_terminating(); //~ ERROR: this function call might not terminate
}

#[pure]
fn pure_fns_need_to_terminate() {
    //~ ERROR: Pure functions need to terminate
}

#[terminates]
fn valid_loop_variant(mut x: i64) {
    while x > 1 {
        body_variant!(Int::new(x));
        x -= 1;
    }
}

#[terminates(Int::new(x))]
fn valid_recursion(x: i64) {
    if x > 0 {
        valid_recursion(x - 1);
    }
}

#[terminates(Int::new(x))]
fn valid_mutual_recursion1(x: i64) {
    if x > 0 {
        valid_mutual_recursion2(x - 1);
    }
}

#[terminates(Int::new(x))]
fn valid_mutual_recursion2(x: i64) {
    if x > 0 {
        valid_mutual_recursion1(x - 1);
    }
}

#[terminates(Int::new(0))]
fn may_have_acyclic_calls_with_increasing_termination_measure(x: i64) {
    valid_mutual_recursion1(x);
}

#[terminates]
fn valid_nested_loop(mut a: i64) {
    while a > 0 {
        body_variant!(Int::new(a));
        let mut b = a;
        while b > 0 {
            body_variant!(Int::new(b));
            b -= 1;
        }
        a -= 1;
    }
}

#[terminates]
fn invalid_nested_inner_loop(mut a: i64) {
    while a > 0 {
        body_variant!(Int::new(a));
        let mut b = a;
        while b > 0 {
            //~ ERROR: this loop might not terminate
            b -= 1;
        }
        a -= 1;
    }
}

#[terminates]
fn invalid_nested_outer_loop(mut a: i64) {
    while a > 0 {
        //~ ERROR: this loop might not terminate
        let mut b = a;
        while b > 0 {
            body_variant!(Int::new(b));
            b -= 1;
        }
        a -= 1;
    }
}

#[terminates]
fn invalid_loop_variant(mut u: i64) {
    while u > 0 {
        body_variant!(Int::new(u)); //~ ERROR: The loop variant might not have decreased
    }
}

#[terminates]
fn y(mut y: i64) {
    while y > 1 {
        body_invariant!(true);
        body_variant!(Int::new(y));
        y -= 1;
    }
}

#[terminates]
#[requires(x >= 0)]
#[ensures(result == fib(x))]
fn fibi(x: i64) -> i64 {
    let mut i = 0;
    let mut a = 0;
    let mut b = 1;
    while i < x {
        body_variant!(Int::new(x) - Int::new(i));
        body_invariant!(i < x);
        body_invariant!(i >= 0);
        body_invariant!(a == fib(i));
        body_invariant!(b == fib(i + 1));
        let c = a + b;
        prusti_assert!(c == fib(i + 2));
        a = b;
        b = c;
        i += 1;
    }
    prusti_assert!(i == x);
    prusti_assert!(a == fib(i));
    a
}

#[pure]
#[requires(x >= 0)]
#[terminates(Int::new(x))]
fn fib(x: i64) -> i64 {
    if x <= 1 {
        x
    } else {
        fib(x - 1) + fib(x - 2)
    }
}
