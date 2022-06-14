// compile-flags: -Punsafe_core_proof=true

#![allow(unused)]

use prusti_contracts::*;
type Map = prusti_contracts::Map<u32, u32>;

fn test0(map: Map) {
    prusti_assert!(map.contains(0) || !map.contains(0));
}

//fn test1(x: u32) {
//    prusti_assert!(!Map::empty().contains(x)); //~ ERROR:
//}
//
//fn test2(map: Map) {
//    prusti_assert!(map.insert(1, 2).contains(1));
//}
//
//fn test3(map: Map) {
//    let map = map.insert(1, 2);
//    let x = map.contains(1);
//    prusti_assert!(x);
//}

fn main() {}
