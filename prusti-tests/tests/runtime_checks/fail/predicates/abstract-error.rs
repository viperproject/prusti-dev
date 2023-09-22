//@rustc-env: PRUSTI_QUIET=true
use prusti_contracts::*;

// This test makes sure that trying to runtime check abstract predicates gives
// a proper error
predicate! {
    #[insert_runtime_check] //~ERROR: Abstract predicates can not be runtime checked
    fn some_abstract_predicate(x: i32) -> bool;
}

fn main() {}
