use prusti_contracts::*;

struct Point {
  x: i32, y: i32
}

#[ensures(old((*p).x + s) == (*result).x)]
#[ensures(old((*p).y) == (*result).y)]
fn shift_x(p: Box<Point>, s:i32) -> Box<Point> {
  Box::new(Point { x: (*p).x + s, y: (*p).y })
}

fn compress(mut segm: (Box<Point>, Box<Point>))
                    -> (Box<Point>, Box<Point>) {
  let mut end = segm.1; // move assignment
  // segm.1 is now inaccessible
  let diff = (*segm.0).x - (*end).x + 1;
  end = shift_x(end, diff);
  segm.1 = end;
  // end is now inaccessible
  assert!((*segm.0).x < (*segm.1).x);
  segm
}

fn main() {}
