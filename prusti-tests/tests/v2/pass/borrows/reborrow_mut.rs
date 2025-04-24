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

fn basic<'l, 's>(num: &'l mut i32) -> &'s mut i32
where 'l: 's
{
    &mut *num
}

fn basic_user() {
    let mut x = 42;
    let y = basic(&mut x);
    // PCG: bb0[8] post_main: Add Abstraction Edge: FunctionCall(DefId(0:3 ~ 58_aurel_pledge[d8c8]::basic), ['?4, '?5]); path conditions: bb0
    *y = 72;
    // PCG: bb1[4] pre_operands: Remove Edge FunctionCall(DefId(0:3 ~ 58_aurel_pledge[d8c8]::basic), ['?4, '?5]) under conditions bb0 -> bb1,
    drop(x);
}

/*
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
    */

fn main() {}
