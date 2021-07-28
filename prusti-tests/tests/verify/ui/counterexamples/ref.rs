// compile-flags: -Pcounterexample=true

use prusti_contracts::*;

#[requires(*x != 0)]
#[ensures(result != 0)]
fn test1(x: &mut i32) -> i32 {
    let mut y = *x;
    y = y * 3 - 12;
    *x = y;
    y
}

#[requires(*x != 0)]
#[ensures(result != 14)]
fn test2(x: &i32) -> i32 {
    let y = *x + 1;
    match y {
        x => x * 2
    }
}

fn main() {}
