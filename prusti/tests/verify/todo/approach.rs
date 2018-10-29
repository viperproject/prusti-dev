#![feature(box_syntax, box_patterns)]
extern crate prusti_contracts;

struct Point {
  x: u32,
  y: u32
}

#[ensures="p.x == old(p.x) + old(s)"]
#[ensures="p.y == old(p.y)"]
fn shift_x(p: &mut Point, s: u32) {
  p.x = p.x + s
}

struct Path {
  current : Point,
  rest : Option<Box<Path>>
}

#[pure]
#[ensures="result > 0"]
fn length(p: &Path) -> u32 {
  1 +
    match p.rest {
      Some(box ref q) => length(q),
      _ => 0
    }
}

#[pure]
#[requires="0 <= n && n < length(p)"]
fn get_nth_x(p: &Path, n: u32) -> u32 {
  if n == 0 {
    p.current.x
  } else {
    match p.rest {
      Some(box ref r) => get_nth_x(r, n-1),
      _ => unreachable!() // we can prove this (FP: not yet in pure functions... we have an open issue)
    }
  }
}

#[requires="0 <= n && n < length(p)"]
//#[ensures="0 <= n && n < length(p)"]
#[ensures="length(p) == old(length(p))"]
#[ensures="forall i: u32 :: (0 <= i && i <= length(p) && i != old(n)) ==> get_nth_x(p, i) == old(get_nth_x(p, i))"]
#[ensures="get_nth_x(p, old(n)) == old(get_nth_x(p, n))"]
fn shift_nth_x(p: &mut Path, n: u32, s:u32) {
  if n == 0 {
    shift_x(&mut p.current, s)
  } else {
    match p.rest {
      Some(box ref mut r) => shift_nth_x(r, n-1, s),
      _ => unreachable!() // we can prove this
    }
  }
}

//fn get_mut(&mut self) -> &mut T; // elided
//fn get_mut<'a>(&'a mut self) -> &'a mut T; // expanded
#[trusted] // TODO: remove this
#[requires="0 <= n && n < length(p)"]
fn borrow_nth(p:&mut Path, n: u32) -> &mut Point {
  if n == 0 {
    & mut p.current
  } else {
    match p.rest {
      Some(box ref mut r) => borrow_nth(r, n-1),
      _ => unreachable!() // we can prove this
    }
  }
}

fn main(){}
