// compile-flags: -Punsafe_core_proof=true 

use prusti_contracts::*;

struct LinkedList {
    val: i32,
    next: Box<LinkedList>,
}

#[ensures(!result)]     //~ ERROR: postcondition might not hold.
fn test_1(x: LinkedList) -> bool {
    x.val == 0
}

#[trusted]
struct WrapperBox<T> {
    inner: Box<T>,
}

struct LinkedList2 {
    val: i32,
    next: WrapperBox<LinkedList>,
}

#[ensures(!result)]     //~ ERROR: postcondition might not hold.
fn test_2(x: LinkedList) -> bool {
    x.val == 0
}

fn main() {}
