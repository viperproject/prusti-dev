// Coverage for `Ord::cmp` / `PartialOrd::partial_cmp` on the `Int` and `Real`
// ghost types, which build `core::cmp::Ordering` (and `Option<Ordering>`)
// snapshots. `Ordering` is compared with the snapshot-equality operator `===`.

use prusti_contracts::*;
use core::cmp::Ordering;

// `Int::cmp` yields each of the three `Ordering` variants.
fn int_cmp() {
    prusti_assert!(Int::from(2).cmp(&Int::from(3)) === Ordering::Less);
    prusti_assert!(Int::from(5).cmp(&Int::from(5)) === Ordering::Equal);
    prusti_assert!(Int::from(9).cmp(&Int::from(4)) === Ordering::Greater);
}

// `Int::partial_cmp` wraps the ordering in `Some`.
fn int_partial_cmp() {
    prusti_assert!(Int::from(2).partial_cmp(&Int::from(3)) === Some(Ordering::Less));
    prusti_assert!(Int::from(5).partial_cmp(&Int::from(5)) === Some(Ordering::Equal));
    prusti_assert!(Int::from(9).partial_cmp(&Int::from(4)) === Some(Ordering::Greater));
}

// The same for `Real`.
fn real_cmp() {
    prusti_assert!(Real::from(1.0).cmp(&Real::from(2.0)) === Ordering::Less);
    prusti_assert!(Real::from(2.0).cmp(&Real::from(2.0)) === Ordering::Equal);
    prusti_assert!(Real::from(3.0).cmp(&Real::from(2.0)) === Ordering::Greater);
}

fn real_partial_cmp() {
    prusti_assert!(Real::from(1.0).partial_cmp(&Real::from(2.0)) === Some(Ordering::Less));
    prusti_assert!(Real::from(2.0).partial_cmp(&Real::from(2.0)) === Some(Ordering::Equal));
    prusti_assert!(Real::from(3.0).partial_cmp(&Real::from(2.0)) === Some(Ordering::Greater));
}

// The ordering agrees with each comparison operator on symbolic arguments.
#[requires(a < b)]
fn agrees_lt(a: Int, b: Int) {
    prusti_assert!(a.cmp(&b) === Ordering::Less);
    prusti_assert!(a.partial_cmp(&b) === Some(Ordering::Less));
}

#[requires(a == b)]
fn agrees_eq(a: Int, b: Int) {
    prusti_assert!(a.cmp(&b) === Ordering::Equal);
    prusti_assert!(a.partial_cmp(&b) === Some(Ordering::Equal));
}

#[requires(a > b)]
fn agrees_gt(a: Int, b: Int) {
    prusti_assert!(a.cmp(&b) === Ordering::Greater);
    prusti_assert!(a.partial_cmp(&b) === Some(Ordering::Greater));
}
