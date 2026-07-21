// The ghost types accept unsized payloads: `Ghost<str>` (as built by the
// `===` desugaring via `Ghost::new_ref`) works on `&str` places.

use prusti_contracts::*;

fn ghost_of_str(a: &str) {
    prusti_assert!(Ghost::new_ref(a) == Ghost::new_ref(a));
}

fn snapshot_eq_str(a: &str) {
    prusti_assert!(*a === *a);
}

fn snapshot_eq_slice(s: &[u8]) {
    prusti_assert!(*s === *s);
}
