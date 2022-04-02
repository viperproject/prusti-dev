//
extern crate prusti_contracts;
use prusti_contracts::*;

fn main() {
    let m0: Map<u32, u32> = Map::empty();
    let m1 = m0.insert(0, 0);
    let m2 = m1.delete(0);
}
