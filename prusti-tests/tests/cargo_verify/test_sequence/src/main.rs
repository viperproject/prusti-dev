//
extern crate prusti_contracts;
use prusti_contracts::*;

fn main() {
    let s0: Seq<u32> = Seq::empty();
    let one = 1;
    let s1: Seq<u32> = Seq::single(one);
    let s2: Seq<u32> = Seq::single(2);
    let s3: Seq<u32> = Seq::concat(Seq::empty(), Seq::empty());
    let s4: Seq<u32> = Seq::concat(s0, s1);
}
