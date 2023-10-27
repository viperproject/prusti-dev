// compile-flags: -Pviper_backend=Lithium
use prusti_contracts::*;

#[requires(forall(|x: i32| x * x >= foo * bar))]
fn test_closure(foo: i32, bar: i32) -> i32 {
    foo + bar + 1
}

fn main() {
    test_closure(0, 0);

    let arg1 = 0;
    let arg2 = 0;
    test_closure(arg1, arg2);
}
