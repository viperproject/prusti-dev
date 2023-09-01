//@run
//@compile-flags: -Pcheck_overflows=false
use prusti_contracts::*;

#[trusted]
fn main() {
    println!("{}", foo(&mut 31)); // expected result: 60
    println!("{}", foo(&mut 1)); // expected result: 0
    println!("{}", foo(&mut 2));
    // should print 3 in theory, but with optimizations enabled
    // we always take the second branch, leading to result: 2
}

// optimally this could be simplified to just:
//  ```
//  let y = x * 2;
//  y
//  ```
//  However, if precondition is violated (as in main:11), the result
//  will be "wrong"
#[requires(*x % 15 == 1)]
fn foo(x: &mut i32) -> i32 {
    *x = *x - 1;
    // prusti thinks: *x % 15 == 0
    let y = *x * 2;
    if *x % 3 != 0 {
        y + 1
    } else if *x % 5 == 0 {
        // if precondition holds we always reach this branch
        y
    } else {
        y - 1
    }
}


