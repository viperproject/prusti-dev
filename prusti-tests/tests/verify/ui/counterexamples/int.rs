// compile-flags: -Pcounterexample=true

use prusti_contracts::*;

#[ensures(result != 86)]
fn test1(x: i32) -> i32 {
    let y = x + 1;
    // TODO: if this assertion is enabled, a counterexample for "result" is
    // displayed with the confusing value 43. At this point, the result CE
    // should not be displayed at all.
    //assert!(y != 43);
    y * 2
}

#[pure]
#[ensures(result != 42)]
fn test2(x: i32) -> i32 {
    x + 21
}

fn main() {}
