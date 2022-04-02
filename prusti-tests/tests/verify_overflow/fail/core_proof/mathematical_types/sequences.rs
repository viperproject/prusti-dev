// compile-flags: -Punsafe_core_proof=true -Ponly_memory_safety=true

use prusti_contracts::*;

fn test1() {
    let s0: Seq<u32> = Seq::empty();
    let one = 1;
    let s1: Seq<u32> = Seq::single(one);
    let s2: Seq<u32> = Seq::single(2);
    let s3: Seq<u32> = Seq::concat(Seq::empty(), Seq::empty());
    let s4: Seq<u32> = Seq::concat(s0, s1);
}

fn test2() {
    assert!(Seq::single(1) == Seq::single(1));  // Needs support for references.
}

fn test3() {
    assert!(Seq::single(1) == Seq::single(2));  //~ERROR
}

fn main() {}
