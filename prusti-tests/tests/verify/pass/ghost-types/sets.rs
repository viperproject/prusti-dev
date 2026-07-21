// Coverage for the `Set<T>` ghost set type: construction (`new`/`single`/
// `set!`), `len`, `contains`, `union`/`intersection`/`difference`,
// `is_subset`, and equality.

use prusti_contracts::*;

// Construction; duplicates collapse and order is irrelevant.
fn construction() {
    prusti_assert!(Set::<i32>::new() == Set::new());
    prusti_assert!(Set::single(5) == set![5]);
    prusti_assert!(set![1, 2] == set![2, 1]);
    prusti_assert!(set![1, 1].len() == Int::from(1));
    prusti_assert!(Set::<i32>::new() != set![1]);
}

// Membership and cardinality.
fn membership() {
    let s = set![1, 2];
    prusti_assert!(s.contains(&1));
    prusti_assert!(s.contains(2));
    prusti_assert!(!s.contains(&3));
    prusti_assert!(s.len() == Int::from(2));
}

// The binary set operations and subset queries.
fn ops() {
    let a = set![1, 2];
    let b = set![2, 3];
    prusti_assert!(a.union(b) == set![1, 2, 3]);
    prusti_assert!(a.intersection(b) == set![2]);
    prusti_assert!(a.difference(b) == set![1]);
    prusti_assert!(set![2].is_subset(a));
    prusti_assert!(!a.is_subset(b));
}

// A set of the mathematical `Int` type.
fn set_of_int() {
    let s = set![Int::from(1), Int::from(2)];
    prusti_assert!(s.contains(&Int::from(1)));
    prusti_assert!(s.len() == Int::from(2));
}
