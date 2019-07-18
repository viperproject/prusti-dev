extern crate prusti_contracts;

struct Point {
    x: i32, y: i32
}

#[ensures="p.x == old(p.x) + old(s)"]
#[ensures="p.y == old(p.y)"]
fn shift_x(p: &mut Point, s: i32) {
    p.x = p.x + s
}

fn align_x_endpoint(
    mut segm: (Box<Point>, Box<Point>)
) -> (Box<Point>, Box<Point>) {
    let end_x = (*segm.1).x;
    shift_x(&mut segm.1, (*segm.0).x - end_x);
    assert!((*segm.0).x == (*segm.1).x);
    segm
}

fn main() {
    let p1 = Box::new(Point { x: 5, y: 5 });
    let p2 = Box::new(Point { x: 8, y: 8 });
    let res = align_x_endpoint((p1, p2));
    //println!("Result: ({},{})-({},{})", res.0.x, res.0.y, res.1.x, res.1.y);
}
