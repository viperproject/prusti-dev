use prusti_contracts::*;

/// Examples from Fabian Wolff's thesis.

// ignore-test
// TODO: history invariants

fn main() {
    let mut count = 0;
    let mut cl = closure!(
        || -> i32 { let r = count; count += 1; r }
    );

    assert_eq!(cl(), 0);
    assert_eq!(cl(), 1);

    // cl is no longer live here
    assert_eq!(count, 2);
}
