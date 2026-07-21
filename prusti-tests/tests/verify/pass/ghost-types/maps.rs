// Coverage for the `Map<K, V>` ghost map type: construction (`new`/`insert`/
// `map!`), indexing, `contains`, `len`, `keys`, `values`, equality, and use
// across function boundaries.

use prusti_contracts::*;

// The empty map contains nothing and has length zero.
fn empty() {
    let m = Map::<i32, i32>::new();
    prusti_assert!(m.len() == Int::from(0));
    prusti_assert!(!m.contains(&5));
    prusti_assert!(m == Map::new());
}

// Construction via `map!`, membership and indexing.
fn construction() {
    let m = map![1 => 10, 2 => 20];
    prusti_assert!(m.contains(&1));
    prusti_assert!(m.contains(&2));
    prusti_assert!(!m.contains(&3));
    prusti_assert!(*m[1] == 10);
    // Indexing accepts both `K` and `&K` (`Value<K>`).
    prusti_assert!(*m[&2] == 20);
    prusti_assert!(m.contains(1));
    prusti_assert!(m.len() == Int::from(2));
}

// Inserting an existing key overwrites without growing the map.
fn insert_overwrite() {
    let m = map![1 => 10];
    let m2 = m.insert(1, 11);
    prusti_assert!(m2.len() == Int::from(1));
    prusti_assert!(*m2[1] == 11);
    prusti_assert!(*m[1] == 10);
}

// `keys` and `values` are the key and value sets.
fn keys_values() {
    let m = map![1 => 10, 2 => 20];
    prusti_assert!(m.keys().contains(&1));
    prusti_assert!(m.keys().contains(&2));
    prusti_assert!(!m.keys().contains(&3));
    prusti_assert!(m.keys().len() == Int::from(2));
    prusti_assert!(m.values().contains(&10));
    prusti_assert!(!m.values().contains(&11));
    prusti_assert!(Map::<i32, i32>::new().keys() == Set::new());
}

// `setminus` removes exactly the given keys, preserving the other entries.
fn setminus() {
    let m = map![1 => 10, 2 => 20, 3 => 30];
    let r = m.setminus(set![1, 3]);
    prusti_assert!(!r.contains(&1));
    prusti_assert!(!r.contains(&3));
    prusti_assert!(r.contains(&2));
    prusti_assert!(*r[2] == 20);
    prusti_assert!(r.keys() == set![2]);
    prusti_assert!(r.len() == Int::from(1));
    prusti_assert!(m.setminus(Set::new()) == m);
    prusti_assert!(m.setminus(m.keys()) == Map::new());
}

// A map with `Int` values.
fn map_of_int() {
    let m = map![1 => Int::from(100)];
    prusti_assert!(*m[1] == Int::from(100));
    prusti_assert!(*m[1] > Int::from(99));
}

// A map as a pure-function argument, related in the contract.
#[pure]
#[requires(m.contains(&0))]
#[ensures(result == m[0])]
fn get_zero(m: Map<i32, i32>) -> Ghost<i32> {
    m[0]
}

fn use_boundary() {
    let m = map![0 => 7, 1 => 8];
    prusti_assert!(*get_zero(m) == 7);
}
