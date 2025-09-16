#![feature(box_patterns)]

use prusti_contracts::*;

/// From points.rs
struct Point {
  x: i32, y: i32
}

/// From points.rs
#[ensures(p.x == old(p.x) + s)]
#[ensures(p.y == old(p.y))]
fn shift_x(p: &mut Point, s: i32) {
  p.x = p.x + s
}

struct Route { //list of Points
  current: Point,
  rest: Option<Box<Route>>
}

#[pure]
#[ensures(result > 0)]
fn length(r: &Route) -> i32 {
  1 + match r.rest {
    Some(box ref q) => length(q),
    None => 0
  }
}

#[pure]
#[requires(0 <= n && n < length(r))]
fn get_nth_x(r: &Route, n: i32) -> i32 {
  if n == 0 { r.current.x } else {
    match r.rest {
      Some(box ref r) => get_nth_x(r, n-1),
      None => unreachable!()
    }
  }
}

#[requires(0 <= n && n < length(r))]
#[ensures(result.x == old(get_nth_x(r, n)))]
// Since a function (with our restrictions) can have only one magic wand
// in its postcondition, we do not require the user to write with which
// reference the functional specification is associated.
#[after_expiry(
    length(r) == old(length(r)) &&
    get_nth_x(r, n) == before_expiry(result.x) &&
    forall(|i: i32| (0<=i && i<length(r) && i != n) ==>
        get_nth_x(r, i) == old(get_nth_x(r, i)))
)]
// See Sec. ~{\texttt{\ref{sec:promises}}}~
fn borrow_nth(r:&mut Route, n: i32) ->
 &mut Point {
  if n == 0 { &mut r.current } else {
    match r.rest {
      Some(box ref mut r) =>
        borrow_nth(r, n-1),
      None => unreachable!()
    }
  }
}

#[requires(0 <= n && n < length(r))]
#[ensures(length(r) == old(length(r)))]
#[ensures(get_nth_x(r, n) == old(get_nth_x(r, n)) + s)]
#[ensures(forall(|i: i32| (0<=i && i<length(r) && i != n) ==> get_nth_x(r, i) == old(get_nth_x(r, i))))]
fn shift_nth_x(r: &mut Route, n: i32, s:i32) {
  let p = borrow_nth(r, n);
  shift_x(p,s);
}

fn main() {}
