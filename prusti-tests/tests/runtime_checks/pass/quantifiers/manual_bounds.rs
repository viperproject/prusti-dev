//@run
use prusti_contracts::*;

#[insert_runtime_check]
#[requires(
    forall(
        |x: usize| (x < 20) ==> true
    )
)]
fn foo() {}

#[insert_runtime_check]
#[requires(
    forall(
        #[runtime_quantifier_bounds(0..20, 12..=22)]
        |x: usize, y: usize| (x < 20) && (y <= 22) && y >= 12 ==> x + y <= 41
    )
)]
fn bar() {}

#[trusted]
fn main() {
    foo();
    bar();
    println!("program intact");
}
