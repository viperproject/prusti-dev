//@run
//@compile-flags: -Pcheck_overflows=false
use prusti_contracts::*;

// for variants we can not really test the behavior if we call an
// optimized version with arguments violating the precondition, because
// matching leads to a switchInt where otherwise points to an unreachable
// block. Altough we might be able to eliminate that one too?

// Test with 3 enums that have the same memory layout:
// (so "bad" casting should not lead to errors)
enum Variants {
    Case1(i32),
    Case2(i32),
    Case3(i32),
}

#[trusted]
fn main() {
    let x = Variants::Case2(5);
    let y = Variants::Case3(42);
    let z = Variants::Case1(72);
    // valid call: expected result 10
    println!("{}", foo(x));
    // valid call: expected result 236
    println!("{}", foo(y));
    // invalid call, without optimizations result would be 72,
    // but because of Case3 to be made into otherwise target,
    // leading to result 216
    println!("{}", foo(z));
}

#[requires(!matches!(x, Variants::Case1(_)))]
fn foo(x: Variants) -> i32 {
    match x {
        Variants::Case1(x) => {
            x
        },
        Variants::Case2(x) => {
            2 * x
        },
        Variants::Case3(x) => {
            3 * x
        }
    }
}
