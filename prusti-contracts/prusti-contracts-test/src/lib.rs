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
