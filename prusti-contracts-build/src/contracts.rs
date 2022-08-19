// TODO: this file has been and is currently ignored
// maybe it was to serve as a compilation-time check that
// our procedural macros don't crash? If so then we probably
// want to move it to `prusti-contracts` somewhere
use prusti_contracts::*;

#[requires(true)]
pub fn test1() {}

#[ensures(true)]
pub fn test2() {}

pub fn test3() {
    for _ in 0..2 {
        body_invariant!(true)
    }
}

#[requires(true)]
#[ensures(true)]
pub fn test4() {
    for _ in 0..2 {
        body_invariant!(true)
    }
}
