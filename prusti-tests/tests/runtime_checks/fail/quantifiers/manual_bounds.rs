//@run: 101
use prusti_contracts::*;

// here the sum can reach 42 and violate this precondition
#[trusted]
#[insert_runtime_check]
#[requires(
    forall(
        #[runtime_quantifier_bounds(0..=20, 12..=22)]
        |x: usize, y: usize| (x <= 20) && (y <= 22) && y >= 12 ==> x + y <= 41
    )
)]
fn bar() {}

#[trusted]
fn main() {
    bar();
    println!("program intact");
}
