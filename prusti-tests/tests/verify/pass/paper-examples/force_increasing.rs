#![feature(box_patterns)]

extern crate prusti_contracts;

struct Point {
    x: i32, y: i32
}

struct Route {
    current: Point,
    rest: Option<Box<Route>>
}

#[pure]
fn max(a: i32, b: i32) -> i32 {
    if a >= b { a } else { b }
}

#[pure]
#[ensures="result > 0"]
fn length(r: &Route) -> i32 {
    1 + match r.rest {
        Some(box ref q) => length(q),
        None => 0
    }
}

#[pure]
#[requires="0 <= n && n < length(r)"]
fn get_nth_x(r: &Route, n: i32) -> i32 {
  if n == 0 { r.current.x } else {
    match r.rest {
      Some(box ref r) => get_nth_x(r, n-1),
      None => unreachable!()
    }
  }
}

#[ensures="length(r) == old(length(r))"]
#[ensures="r.current.x == max(old(r.current.x), min_x)"]
#[ensures="r.current.y == old(r.current.y)"]
#[ensures="forall i: i32 :: (1 <= i && i < length(r)) ==> get_nth_x(r, i) == max(get_nth_x(r, i - 1), old(get_nth_x(r, i)))"]
fn force_increasing(r: &mut Route, min_x: i32) {
    r.current.x = max(r.current.x, min_x);
    if let Some(box ref mut rest) = r.rest {
        force_increasing(rest, r.current.x);
    } else {
	    assert!(length(r) == 1);
	}
}

fn main(){}
