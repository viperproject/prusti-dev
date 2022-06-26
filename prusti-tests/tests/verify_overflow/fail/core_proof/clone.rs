// compile-flags: -Punsafe_core_proof=true
// ignore-test: #1065

use prusti_contracts::*;

fn main() {}

#[derive(Clone)]
struct Container<T>(T);
