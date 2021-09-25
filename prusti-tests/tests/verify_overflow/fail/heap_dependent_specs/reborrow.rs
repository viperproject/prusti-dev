use prusti_contracts::*;

pub struct Point {
    x: i32,
    y: i32,
}

#[pure]
fn reborrow(s: &Point) -> &i32 {
    &s.x
}

#[ensures(*reborrow(&result) == 1)]
fn test() -> Point {
    let p = Point {
        x: 1,
        y: 2,
    };
    p
}

#[ensures(*reborrow(&result) == 2)] //~ ERROR: postcondition might not hold
fn test2() -> Point {
    let p = Point {
        x: 1,
        y: 2,
    };
    p
}

fn main() {}
