use prusti_contracts::*;

predicate! {
    fn false_p() -> bool {
        false
    }
}

#[requires(false_p())]
fn precond_fail() {}

fn main() {
    precond_fail(); //~ ERROR precondition might not hold
}
