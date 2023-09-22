//@run
use prusti_contracts::*;

#[derive(Clone)]
struct SomeStruct(i32);

fn main() {
    let s = SomeStruct(42);
    foo(s);
}

#[trusted]
fn foo(mut s: SomeStruct) {
    s.0 = 52;
    // fails because evaluated in old state
    prusti_assert!({ old(s.0) == 42});
}
