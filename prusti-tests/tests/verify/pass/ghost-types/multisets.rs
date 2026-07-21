// Coverage for the `Multiset<T>` ghost multiset type: construction (`new`/
// `single`/`multiset!`), `len` (with multiplicity), `contains` (the
// multiplicity), `union`/`intersection`/`difference`, `is_subset`, and
// equality.

use prusti_contracts::*;

// Construction; duplicates count, order is irrelevant.
fn construction() {
    prusti_assert!(Multiset::<i32>::new() == Multiset::new());
    prusti_assert!(Multiset::single(5) == multiset![5]);
    prusti_assert!(multiset![1, 2] == multiset![2, 1]);
    prusti_assert!(multiset![1, 1].len() == Int::from(2));
    prusti_assert!(multiset![1] != multiset![1, 1]);
}

// `contains` is the multiplicity of the element.
fn count() {
    let m = multiset![1, 1, 2];
    prusti_assert!(m.contains(&1) == Int::from(2));
    prusti_assert!(m.contains(1) == Int::from(2));
    prusti_assert!(m.contains(&2) == Int::from(1));
    prusti_assert!(m.contains(&3) == Int::from(0));
}

// The binary multiset operations and subset queries.
fn ops() {
    let a = multiset![1, 2];
    let b = multiset![2, 3];
    prusti_assert!(a.union(b) == multiset![1, 2, 2, 3]);
    prusti_assert!(a.intersection(b) == multiset![2]);
    prusti_assert!(a.difference(b) == multiset![1]);
    prusti_assert!(multiset![2].is_subset(a));
    prusti_assert!(!multiset![2, 2].is_subset(a));
}
