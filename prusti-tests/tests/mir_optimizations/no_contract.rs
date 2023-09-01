//@run
//@compile-flags: -Pcheck_overflows=false
use prusti_contracts::*;

// takeaway: we need a better example!
#[trusted]
fn main() {
    let mut x = 0;
    for i in 0..i32::MAX/5 {
        x += foo(i);
    }
    println!("x: {x}");
}

// Example of a function where a traditional compiler might struggle,
// but with prusti we can simplify this to just:
// ```
// fn foo(x: i32) -> i32 {
//     30
// }
// ```
// Note: actually it seems like llvm performs this optimization too..
// This test doesn't really check that the optimization is actually
// performed, but rather that it doesn't break the program.
// To make sure it is performed we need to inspect the MIR.
fn foo(x: i32) -> i32 {
    let mut y = 0;
    // a set of operations that in the end, will not modify y
    y = y + x;
    let z = 4 * x;
    y = y - z;
    y = y + (3 * x);

    if y != 0 {
        // unreachable!
        return 42
    } else {
        return 1
    }
}

