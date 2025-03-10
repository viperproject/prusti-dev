use prusti_contracts::*;

/*
fn double_tuple<'a>(x: &'a mut (i32, (i32, i32))) -> &'a mut i32
where
    'a: 'a,
{
    &mut x.1.0
}

fn tuple<'a>(x: &'a mut (i32, i32)) -> &'a mut i32
where
    'a: 'a,
{
    &mut x.0
}
*/
/*
// TODO: fails because wands expect the blocked argument to be a mutref
struct Container<'a> {
    x: &'a mut i32,
}
#[after_expiry(*c.x == before_expiry(*result))]
fn use_container<'a, 'b: 'a>(c: Container<'b>) -> &'a mut i32 {
    c.x
}
*/
struct Point {
    x: i32,
    y: i32,
}

#[after_expiry((pt.y == old(pt.y)) & (pt.x == before_expiry(*result)))]
fn get_mut_x<'a, 'b: 'a>(pt: &'b mut Point) -> &'a mut i32 {
    &mut pt.x
}

fn reborrow_user() {
    let mut pt = Point { x: 42, y: 72 };
    let y = get_mut_x(&mut pt);
    *y = 72;
    assert!(pt.x == pt.y);
}

fn main() {}
