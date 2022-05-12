// compile-flags: -Punsafe_core_proof=true

use prusti_contracts::*;

type Map = prusti_contracts::Map<u32, u32>;

#[requires(_val)]
fn requires_true(_val: bool) {}

#[pure]
#[trusted]
fn empty() -> (u32, u32) {
    (2, 2)
}

#[requires(Map::empty() == Map::empty())]
fn test1() {}

#[requires(empty() == empty())]
fn test2() {}

fn checks_preconditions() {
    test1();
}

#[ensures(Map::empty().insert(0, 0) == Map::empty().insert(0, 1))] //~ ERROR
fn should_fail() {}

#[ensures(Map::empty().insert(0, 0) == Map::empty().insert(0, 0))]
fn should_pass1() {}

// FIXME: viper bug
//#[ensures(Map::empty().insert(0, 0).insert(1, 1) == Map::empty().insert(1, 1).insert(0, 0))]
fn should_pass2() {}

// FIXME
// #[ensures(Map::empty().len() == Int::new(0))]
// #[ensures(Map::empty().insert(1, 2).len() == Int::new(1))]
fn map_len() {}

#[ensures(Map::empty().insert(0, 1).lookup(0) == 1)]
#[ensures(Map::empty().insert(0, 1).insert(0, 2).lookup(0) == 2)]
fn map_lookup() {}

fn map_construction() {
    // FIXME
    // let map = Map::empty();
}

fn main() {}
