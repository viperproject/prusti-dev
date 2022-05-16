// compile-flags: -Punsafe_core_proof=true

use prusti_contracts::*;

type Seq = prusti_contracts::Seq<i32>;

#[ensures(Seq::empty().len() == Int::new(0))]
fn test1() {}

#[ensures(Seq::empty().len() == Int::new(1))]   //~ ERROR: postcondition might not hold.
fn test2() {}

#[ensures(Seq::empty() == Seq::empty())]
#[ensures(Seq::single(1) == Seq::single(1))]
#[ensures(Seq::concat(Seq::single(1), Seq::single(2)) == Seq::concat(Seq::single(1), Seq::single(2)))]
fn seq_eq1() {}

#[ensures(Seq::single(1) == Seq::single(2))] //~ ERROR: postcondition might not hold.
fn seq_eq2() {}

fn main() {}
