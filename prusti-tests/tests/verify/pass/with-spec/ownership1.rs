#![feature(nll)]
#![feature(box_patterns, box_syntax)]

use prusti_contracts::*;

struct Point {
    x: u32,
    y: u32,
}

#[trusted]
#[ensures(result.x == old(p.x + d))]
#[ensures(result.y == old(p.y))]
fn shift_x(p: Point, d: u32) -> Point {
    unimplemented!()
}

#[ensures(result.0.x == old(line.0.x))]
#[ensures(result.0.y == old(line.0.y))]
#[ensures(result.1.x == old(line.1.x + d))]
#[ensures(result.1.y == old(line.1.y))]
fn shift_end(mut line: (Point, Point), d: u32) -> (Point, Point) {
    let end = line.1;
    // l.start is now inaccessible
    let new_end = shift_x(end, d);
    line.1 = new_end;
    line
}

fn main(){}
