use prusti_contracts::*;

pub struct Point {
    x: i32,
    y: i32,
}

#[pure]
fn reborrow(s: &Point) -> &i32 {
    &s.x
}

fn main() {}
