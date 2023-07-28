// compile-flags: -Punsafe_core_proof=true

#![allow(unused)]

use prusti_contracts::*;

#[terminates]
fn main() {
    while false {
        body_invariant!(false);
        body_variant!(Int::new(0));
    }
}

fn ghost_terminates() {
    ghost! {
        while false {
            body_invariant!(false);
            body_variant!(Int::new(0));
        }
    };
}

fn ghost_nontermination_error() {
    ghost! {
        loop { //~ ERROR: this loop might not terminate
        }
    };
}

#[terminates]
fn non_reachable_nontermination_is_allowed() {
    if false {
        loop {}
    }
}

#[pure]
#[terminates]
fn pure_fn() -> u32 {
    42
}

fn impure_fn() -> u32 {
    42
}

fn allows_pure_calls() {
    ghost! {
        let x = pure_fn();
    };
}

fn disallows_impure_calls() {
    ghost! {
        let x = impure_fn(); //~ ERROR: Only pure function calls are allowed in ghost blocks.
    };
}

#[terminates]
fn terminating_fn() {}

#[terminates]
fn terminating_fns_can_only_call_terminating_fns_1() {
    terminating_fn();
}

fn nonterminating_fn() {
    loop {}
}

#[terminates]
fn terminating_fns_can_only_call_terminating_fns_2() {
    nonterminating_fn(); //~ ERROR
    let x = 5;
}

#[terminates]
fn recursion_disallowed() {
    recursion_disallowed(); //~ ERROR
}

#[terminates]
fn mutual_recursion_disallowed1() {
    mutual_recursion_disallowed2(); // FIXME: This should be an error.
}

#[terminates]
fn mutual_recursion_disallowed2() {
    mutual_recursion_disallowed1(); // FIXME: This should be an error.
}

//thread 'rustc' panicked at 'internal error: entered unreachable code: cannot convert abstract type into a memory block: impl_Fn()$0', prusti-viper/src/encoder/middle/core_proof/builtin_methods/interface.rs:2527:62
//#[terminates]
//fn closures_disallowed(x: impl Fn()) {
//    x(); //FIXME ERROR
//}
