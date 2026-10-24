use prusti_contracts::*;

#[pure]
#[trusted]
fn f(x: i32) -> i32 { 0 }

#[pure]
#[trusted]
fn g(x: i32) -> i32 { 0 }

/// The trigger is never matched, so the quantifier is not instantiated even
/// though its body would give the assertion.
#[requires(forall(|i: i32| f(i) > 0, triggers = [(g(i),)]))]
fn restrictive(x: i32) {
    prusti_assert!(f(3) > 0); //~ERROR: assertion might not hold
}
