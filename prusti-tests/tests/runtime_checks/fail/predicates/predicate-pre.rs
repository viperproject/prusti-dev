//@run: 101
use prusti_contracts::*;

#[trusted]
fn main() {
    foo(42);
    foo(41);
}
predicate! {
    #[insert_runtime_check]
    fn is_even(x: i32) -> bool {
        x % 2 == 0
    }
}

#[insert_runtime_check]
#[requires(is_even(x))]
fn foo(x: i32) {}
