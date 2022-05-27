use prusti_contracts::*;

#[requires(x > 100)]
fn foo(x: u32) {
    let _ = x;
    // ...
}

pub fn main() {
    foo(0); //~ ERROR: precondition might not hold
}
