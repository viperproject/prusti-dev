#![feature(nll)]
#![feature(box_patterns)]

use prusti_contracts::*;

struct Point {
    x: Box<u32>,
    y: Box<u32>,
}

#[requires(u32::MAX - *a >= b)]
#[ensures(*result == old(*a) + old(b))]
fn add(a: Box<u32>, b: u32) -> Box<u32> { Box::new(*a + b) }

#[requires(u32::MAX - *p.x >= s)]
#[ensures(*result.x == old(*p.x) + old(s))]
#[ensures(*result.y == old(*p.y))]
fn shift_x(p: Point, s: u32) -> Point {
    let mut pp = p;
    let x = pp.x;     // p.x is moved out.
    pp.x = add(x, s); // x is moved into add,
                      // result moved into p.x
    pp
}

fn main() {}
