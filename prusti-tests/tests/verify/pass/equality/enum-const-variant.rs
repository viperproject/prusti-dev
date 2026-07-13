// Regression test for encoding enum constants: the variant's fields must be
// projected on the variant's own layout (after a downcast), not the enum's
// layout. For a niche-optimised enum such as `Option<E>`, projecting the
// payload without the downcast reinterpreted it with the wrong layout, so a
// constant like `Some(E::B)` was mis-encoded as `Some(E::A)`. This only
// surfaced for non-first variants compared against a run-time-built value.

use prusti_contracts::*;

#[derive(Copy, Clone)]
enum E {
    A,
    B,
    C,
}

#[pure]
fn mk(x: i32) -> E {
    if x == 0 {
        E::A
    } else if x == 1 {
        E::B
    } else {
        E::C
    }
}

// A run-time-selected fieldless-enum value against each variant constant.
fn bare_variants() {
    prusti_assert!(mk(0) === E::A);
    prusti_assert!(mk(1) === E::B);
    prusti_assert!(mk(2) === E::C);
}

#[pure]
fn mk_opt(x: i32) -> Option<E> {
    Some(mk(x))
}

// The same nested inside a niche-optimised `Option`, against `Some(_)`
// constants (the case that previously mis-encoded non-first variants).
fn niche_option() {
    prusti_assert!(mk_opt(0) === Some(E::A));
    prusti_assert!(mk_opt(1) === Some(E::B));
    prusti_assert!(mk_opt(2) === Some(E::C));
}

// A payload-carrying enum: the field is read from the correct variant layout.
#[pure]
fn mk_payload(x: i32) -> Option<i32> {
    if x >= 0 {
        Some(x)
    } else {
        None
    }
}

fn payload_variants() {
    prusti_assert!(mk_payload(7) === Some(7));
    prusti_assert!(mk_payload(-1) === None);
}
