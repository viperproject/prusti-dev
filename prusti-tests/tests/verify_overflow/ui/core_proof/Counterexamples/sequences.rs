// compile-flags: -Punsafe_core_proof=true -Pcounterexample=true

#![allow(unused)]

use prusti_contracts::*;
//a counterexample can only be generated for directly accessed elements of a sequence

fn test1(seq: Seq<i32>, idx: usize) {
    //the counterexample only shows a seq of length <= idx but the elements are unkown
    prusti_assert!(seq[idx] == seq[idx]);
}

#[requires(idx >= Int::new(0))]
#[requires(idx < seq1.len())]
#[requires(seq1.len() == seq2.len())]
fn test2(seq1: Seq<i32>, seq2: Seq<i32>, idx: Int) {
    prusti_assert!(seq1[idx] == seq1[idx]);
}

fn test3() {
    let seq = seq![1, 2, 3, 4, 5];
    prusti_assert!(seq[2] == 4);
}

#[requires(seq.len() == Int::new(2))]
fn test4(a: i32, b: i32, seq: Seq<i32>) {
    //the counterexample only contains values for a and b but not for the elements of seq
    prusti_assert!(seq == Seq::concat(Seq::single(a), Seq::single(b)));
}

fn main() {}
