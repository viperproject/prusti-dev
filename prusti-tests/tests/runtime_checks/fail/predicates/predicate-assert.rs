//@run: 101
use prusti_contracts::*;

// This test has 2 purposes:
// 1. Prusti's specification checker makes sure that predicates are not called from
// normal user code. With runtime checks this got a bit more complicated, since now
// predicates can (sometimes, after ast rewriting) be called from within user code.
// But then they're in a block starting with a #[check_only] marked closure. This test
// makes sure prusti properly recognizes this block
// 2. It also checks that the runtime check is properly executed and inserted
predicate!{
    #[insert_runtime_check]
    fn even(x: i32) -> bool {
        x % 2 == 0
    }
}

#[trusted]
fn main() {
    prusti_assert!(#[insert_runtime_check] even(3));
}
