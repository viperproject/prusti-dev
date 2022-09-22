#![allow(unused)]

use prusti_contracts::{self as pc, *};

type Seq = prusti_contracts::Seq<u32>;

fn empty_seq_zero_len() {
    prusti_assert!(Seq::empty().len() == Int::new(0));
}

fn empty_seq_not_one_len() {
    prusti_assert!(Seq::empty().len() == Int::new(1)); //~ ERROR: asserted expression might not hold
}

fn seq_eq1() {
    prusti_assert!(Seq::empty() == Seq::empty());
    prusti_assert!(Seq::single(1) == Seq::single(1));
    prusti_assert!(
        Seq::concat(Seq::single(1), Seq::single(2)) == Seq::concat(Seq::single(1), Seq::single(2))
    );
}

fn seq_eq2() {
    prusti_assert!(Seq::single(1) == Seq::single(2)); //~ ERROR: asserted expression might not hold
}

fn seq_construction() {
    let seq: pc::Seq<pc::Seq<Int>> = pc::Seq::empty();
}

fn main() {}
