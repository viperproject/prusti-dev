// compile-flags: -Punsafe_core_proof=true

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

fn random_indexing_fails_usize(seq: Seq, idx: usize) {
    prusti_assert!(seq[idx] == seq[idx]); //~ ERROR: the sequence index may be out of bounds
}

#[requires(idx >= Int::new(0))]
fn random_indexing_fails_int(seq: Seq, idx: Int) {
    prusti_assert!(seq[idx] == seq[idx]); //~ ERROR: the sequence index may be out of bounds
}

fn indexing() {
    let seq = seq![1, 2, 3, 4, 5];
    prusti_assert!(seq[2] == 3);
}

fn seq_macro() {
    prusti_assert!(seq![1, 2] == Seq::concat(Seq::single(1), Seq::single(2)));
}

fn main() {}
