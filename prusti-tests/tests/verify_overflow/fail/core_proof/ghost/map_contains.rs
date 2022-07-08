// compile-flags: -Punsafe_core_proof=true

#![allow(unused)]

use prusti_contracts::*;
type Map = prusti_contracts::Map<u32, u32>;

fn test0(map: Map) {
    prusti_assert!(map.contains(0) || !map.contains(0));
}

fn test1(x: u32) {
    prusti_assert!(Map::empty().contains(x)); //~ ERROR: the asserted expression might not hold
}

fn test2(map: Map) {
    prusti_assert!(map.insert(1, 2).contains(1));
}

fn test3(map: Map) {
    let map = map.insert(1, 2);
    let x = map.contains(1);
    prusti_assert!(x);
}

#[requires(map.contains(2))]
unsafe fn test4(map: Map) {
    let x = map.lookup(2);
}

#[requires(map.contains(2))]
fn test5(map: Map) {
    if map.contains(2) {
        let x = map.lookup(2);
    } else {
        unreachable!();
    }
}

fn test6(map: Map) {
    let x = map.lookup(2); //~ ERROR: the key might not be in the map
}

fn main() {}
