#![allow(unused)]

use prusti_contracts::{self as pc, *};

type Seq = prusti_contracts::Seq<u32>;

fn empty_seq_zero_len() {
    prusti_assert!(Seq::empty().len() == Int::new(0));
}

fn main() {}
