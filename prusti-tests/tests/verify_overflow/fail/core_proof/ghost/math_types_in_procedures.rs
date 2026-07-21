//@ compile-flags: -Punsafe_core_proof=true

#![allow(unused)]

use prusti_contracts::*;
type Map = prusti_contracts::Map<u32, u32>;
type Seq = prusti_contracts::Seq<u32>;

macro_rules! do_the_thing {
    ($($expr:expr;)*) => {$(
        let var = $expr;
        prusti_assert!(var == $expr);
    )*}
}

fn test0() {
    let seq = seq![1, 2, 1, 5];
    let x = *seq[0];
    let y = *seq[2];
    prusti_assert!(x == y);
}

fn test1() {
    prusti_assert!(*Seq::single(0)[0] == 1); //~ ERROR: the asserted expression might not hold
}

fn basic_test() {
    do_the_thing! {
        Seq::new();
        seq![1];
        seq![1, 2, 3];
        Map::new();
        map![0 => 1, 3 => 5];
        Int::from(0) + Int::from(1);
        Int::from(0) - Int::from(1);
        Int::from(0) * Int::from(1);
        Int::from(0) / Int::from(1);
        Int::from(0) % Int::from(1);
        map![1 => 1, 0 => 2][1];
        seq![1, 2, 3][1];
    }
}

fn vars_used_in_fns() {
    let s1 = Seq::single(1);
    let s2 = seq![2, 3];
    let s3 = s1.append(s2);
    prusti_assert!(s3 == seq![1, 2, 3]);
}

fn main() {}
