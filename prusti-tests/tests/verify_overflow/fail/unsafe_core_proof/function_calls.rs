// compile-flags: -Punsafe_core_proof=true

use prusti_contracts::*;
fn main() {}

fn f1(x: &mut i32){}
fn function_call_one_arg() {
    let mut a = 1;
    let x = f1(&mut a);
}
fn function_call_one_arg_assert_false() {
    let mut a = 1;
    let x = f1(&mut a);
    assert!(false);      //~ ERROR: the asserted expression might not hold
}

fn f2<'b:'a, 'a>(x: &'a mut i32, y: &'b mut i32){}
fn function_call_two_arg() {
    let mut a = 1;
    let mut b = 1;
    let x = f2(&mut a, &mut b);
    a = 4;
}
fn function_call_two_arg_assert_false() {
    let mut a = 1;
    let mut b = 1;
    let x = f2(&mut a, &mut b);
    a = 4;
    assert!(false);      //~ ERROR: the asserted expression might not hold
}

fn f3<'a, 'b>(x: &'a mut i32, y: &'b mut i32){
    *x = 2;
    *y = 2;
}
fn function_call_two_arg_with_modifiction() {
    let mut a = 1;
    let mut b = 1;
    let x = f3(&mut a, &mut b);
    a = 3;
    b = 3;
}
fn f3_assert_false<'a, 'b>(x: &'a mut i32, y: &'b mut i32){
    *x = 2;
    *y = 2;
    assert!(false);      //~ ERROR: the asserted expression might not hold
}
fn function_call_two_arg_with_modifiction_assert_false() {
    let mut a = 1;
    let mut b = 1;
    let x = f3_assert_false(&mut a, &mut b);
    a = 3;
    b = 3;
    assert!(false);      //~ ERROR: the asserted expression might not hold
}

fn f4(x: &mut i32) -> i32{
    *x
}
fn function_call_return_value() {
    let mut a = 1;
    let x = f4(&mut a);
}
fn function_call_return_value_assert_false() {
    let mut a = 1;
    let x = f4(&mut a);
    assert!(false);      //~ ERROR: the asserted expression might not hold
}

fn f5<'a>(x: &'a mut i32) -> &'a mut i32{
    x
}
fn function_call_return_ref() {
    let mut a = 1;
    let aa = f5(&mut a);
    *aa = 2;
}
fn function_call_return_ref_assert_false() {
    let mut a = 1;
    let aa = f5(&mut a);
    *aa = 2;
    assert!(false);      //~ ERROR: the asserted expression might not hold
}

fn f6<'a, 'b>(x: &'a mut i32, y: &'b mut i32) -> &'b mut i32{
    y
}
fn function_call_return_ref_2() {
    let mut a = 1;
    let mut b = 2;
    let bb = f6(&mut a, &mut b);
    *bb = 3;
}
fn function_call_return_ref_2_assert_false() {
    let mut a = 1;
    let mut b = 2;
    let bb = f6(&mut a, &mut b);
    *bb = 3;
    assert!(false);      //~ ERROR: the asserted expression might not hold
}
