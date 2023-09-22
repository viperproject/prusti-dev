//@run: 101
use prusti_contracts::*;

fn main() {
    // fails
    prusti_assume!(#[insert_runtime_check] false);
    prusti_assert!(#[insert_runtime_check] false);
}
