extern crate prusti_contracts;

struct Point {
  x: i32, y: i32
}

#[ensures="p.x == old(p.x) + old(s)"]   // TODO: Remove old around s.
#[ensures="p.y == old(p.y)"]
fn shift_x(p: &mut Point, s: i32) {
  p.x = p.x + s
}

/*
fn client(mut p: Point, mut q: Point) {
    p.y = q.y;
    let s = q.x - p.x;
    shift_x(&mut p, s);
    assert!(p.x == q.x && p.y == q.y);
}
*/

fn main() {}
