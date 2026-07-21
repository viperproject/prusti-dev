// Failing verification conditions in and around `ghost!` blocks: assertions
// inside ghost bodies are checked, ghost values are constrained to the body's
// value (not arbitrary), contracts of functions called from ghost code are
// enforced, and ghost bodies must not panic.

use prusti_contracts::*;

fn failing_assert_in_ghost() {
    ghost! {
        let x = Int::from(2) + Int::from(2);
        prusti_assert!(x == Int::from(5)); //~ERROR: assertion might not hold
    };
}

// The block's value is the body's value: a wrong claim about it must fail.
fn ghost_value_is_constrained() {
    let x = ghost! { Int::from(1) };
    prusti_assert!(*x === Int::from(2)); //~ERROR: assertion might not hold
}

#[requires(x < 100)]
fn bounded(x: i64) -> i64 {
    x
}

// Contracts of functions called inside a ghost body are enforced.
fn precondition_in_ghost() {
    ghost! {
        let _v = bounded(200); //~ERROR: precondition might not hold
    };
}

// Ghost code must not panic.
fn panic_in_ghost(x: i64) {
    ghost! {
        assert!(x == 0); //~ERROR: precondition might not hold
    };
}

// Checked (partial) collection operations are also checked inside a pure
// function's ghost block, via the function's method encoding.
#[pure]
fn out_of_bounds_in_pure_ghost() -> Ghost<i32> {
    ghost! { *seq![1, 2][Int::from(5)] } //~ERROR: the sequence index may be out of bounds
}
