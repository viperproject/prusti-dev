// compile-flags: -Punsafe_core_proof=true

use prusti_contracts::*;

fn test_construct_maps() {
    ghost! {
        //let m0: Map<u32, u32> = Map::empty();
        //let m1 = m0.insert(0, 0);
        //let m2 = m1.delete(0);
        assert!(Map::<u32, u32>::empty() == Map::<u32, u32>::empty());
    }
}

//fn test_maps_eq() {
//    ghost! {
//        let m0 = Map::empty().insert(0, 0);
//        let m1 = Map::empty().insert(0, 0);
//        assert!(m0 == m1);
//    }
//}
//
//fn test_maps_neq() {
//    ghost! {
//        let m0 = Map::empty().insert(0, 0);
//        let m1 = Map::empty().insert(0, 1);
//        assert!(m0 == m1);  // ~ERROR
//    }
//}
//
fn main() {}
