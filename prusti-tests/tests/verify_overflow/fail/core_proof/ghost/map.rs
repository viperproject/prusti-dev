// compile-flags: -Punsafe_core_proof=true

#![allow(unused)]

use prusti_contracts::*;
type Map = prusti_contracts::Map<u32, u32>;

fn should_fail() {
    prusti_assert!(false); //~ ERROR: the asserted expression might not hold
}

fn trivial_pass1() {
    prusti_assert!(Map::empty() == Map::empty());
}

fn trivial_pass2() {
    prusti_assert!(Map::empty().insert(0, 1) == Map::empty().insert(0, 1));
}

fn trivial_fail() {
    prusti_assert!(Map::empty().insert(0, 0) == Map::empty()); //~ ERROR: the asserted expression might not hold
}

#[requires(k1 != k2)]
fn commutativity(k1: u32, v1: u32, k2: u32, v2: u32) {
    prusti_assert!(map![k1 => v1, k2 => v2] == map![k2 => v2, k1 => v1]);
}

fn map_len(m1: Map, k: u32, v: u32) {
    prusti_assert!(Map::empty().len() == Int::new(0));
    prusti_assert!(map![0 => 0].len() == Int::new(1));

    prusti_assert!(
        m1.insert(k, v).len() == m1.len() || m1.insert(k, v).len() == m1.len() + Int::new(1)
    );

    prusti_assert!(Map::empty().insert(0, 0).len() == Int::new(2)); //~ ERROR: the asserted expression might not hold
}

fn map_lookup(m: Map, k: u32, v1: u32, v2: u32) {
    prusti_assert!(m.insert(k, v1).insert(k, v2)[k] == v2);
    prusti_assert!(m.insert(k, v1)[k] == v1);
    prusti_assert!(m[k] == m[k]) //~ ERROR:
}

fn map_construction() {
    let map1 = Map::empty();
}

fn main() {}
