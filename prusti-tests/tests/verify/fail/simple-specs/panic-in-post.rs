use prusti_contracts::*;

#[requires(x != 0)]
#[ensures({
    assert!(x != 0); // OK
    true
})]
fn good(x: u32) {}

#[ensures({
    assert!(x != 0); //~ ERROR postcondition might not hold
    true
})]
fn bad(x: u32) {}

fn main() {}
