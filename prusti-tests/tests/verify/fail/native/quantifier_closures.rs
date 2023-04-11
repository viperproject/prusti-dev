// compile-flags: -Pviper_backend=Lithium
use prusti_contracts::*;

#[requires(forall(|x: i32| x * x >= foo * bar))] //~ ERROR precondition might not hold
fn test_closure_1(foo: i32, bar: i32) -> i32 {
    foo + bar + 1
}

#[requires(forall(|x: i32| x * x >= foo * bar))] //TODO: both errors reported
fn test_closure_2(foo: i32, bar: i32) -> i32 {
    foo + bar + 1
}

fn main() {
    test_closure_1(5, 3); //TODO: error reported here

    let arg1 = 1;
    let arg2 = 2;
    test_closure_2(arg1, arg2); //TODO: error reported here
}
