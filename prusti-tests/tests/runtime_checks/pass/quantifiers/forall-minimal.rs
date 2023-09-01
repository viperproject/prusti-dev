//@run
use prusti_contracts::*;

#[insert_runtime_check]
#[requires(forall(|x: usize| (x < 20) ==> true))]
fn foo() {}

fn main() {
    foo();
}
