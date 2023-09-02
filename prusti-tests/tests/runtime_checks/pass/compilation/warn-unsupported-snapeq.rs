//@compile-flags: -Pcheck_overflows=false -Phide_uuids=true -Pquiet=true
//@check-pass
use prusti_contracts::*;

#[trusted]
fn main() {
    let s1 = S { x: 1 };
    let s2 = S { x: 1 };
    foo(s1, s2);
}

// this should generate a warning, since snapshot equality currently
// is not checked correctly at runtime. Unfortunately the emitted
// warning is currently not properly parsed by ui_test
// if annotated with a comment.
#[insert_runtime_check]
#[requires(x === y)]
fn foo(x: S, y: S) -> i32 {
    x.x + y.x
}

struct S {
    x: i32,
}
