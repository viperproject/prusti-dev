//@compile-flags: -Pquiet=true
use prusti_contracts::*;

// For this predicate to be checkable at runtime, the one it calls would also have to
// be checkable.
predicate!{
    #[insert_runtime_check]
    fn not_even(x: i32) -> bool {
        !even(x) //~ ERROR: Referring to predicate that is not runtime checkable
    }
}

predicate!{
    // #[insert_runtime_check] // this would fix it
    fn even(x: i32) -> bool {
        x % 2 == 0
    }
}

fn main() {}
