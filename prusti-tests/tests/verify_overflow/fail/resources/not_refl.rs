// ignore-test
use prusti_contracts::*;
#[invariant_twostate(self.value == old(self.value) + 1)]
struct Counter { value : u32}

fn main(){}
