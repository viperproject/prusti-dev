use prusti_contracts::*;

fn deref_mut() {
    let mut x = Box::new(1);
    *x = 5;
    assert!(*x == 5);
    let v = *x;
    assert!(v == 5);
}

fn move_out() {
    let b = Box::new(Box::new(11));
    let inner = *b;
    assert!(*inner == 11);
}

struct Point {
    x: i32,
    y: i32,
}

fn field_access() {
    let mut p = Box::new(Point { x: 1, y: 2 });
    p.x = 10;
    assert!(p.x == 10 && p.y == 2);
}

#[ensures(**b == 3)]
fn write_behind_ref(b: &mut Box<i32>) {
    **b = 3;
}

fn call_write_behind_ref() {
    let mut b = Box::new(0);
    write_behind_ref(&mut b);
    assert!(*b == 3);
}

#[ensures(***b == old(***b) + 1)]
fn incr_nested(b: &mut Box<Box<i32>>) {
    ***b += 1;
}

fn call_incr_nested() {
    let mut b = Box::new(Box::new(41));
    incr_nested(&mut b);
    assert!(**b == 42);
}

#[ensures(*result === x)]
fn box_generic<T>(x: T) -> Box<T> {
    Box::new(x)
}

fn call_box_generic() {
    let b = box_generic(9);
    assert!(*b == 9);
}

#[pure]
fn read_box(b: &Box<i32>) -> i32 {
    **b
}

#[requires(read_box(&b) == 4)]
fn takes_box(b: Box<i32>) {
    assert!(*b == 4);
}

fn call_takes_box() {
    takes_box(Box::new(4));
}
