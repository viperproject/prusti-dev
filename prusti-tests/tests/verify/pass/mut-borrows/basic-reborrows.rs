#![feature(box_patterns)]

use prusti_contracts::*;

struct T {
    f: u32,
}

struct U {
    f: u32,
    g: u32,
}

#[requires(_a.f == 4)]
fn check_t(_a: T) {}

#[requires(_a.f == 3 && _a.g == 4)]
fn check_u(_a: U) {}

#[ensures(*result == old(*x))]
#[after_expiry(before_expiry(*result) == *x)]
fn reborrow_u32(x: &mut u32) -> &mut u32 {
    x
}

fn reborrow_T(x: &mut T) -> &mut T {
    x
}

fn borrow_u32(_x: &mut u32) {
}

pub fn test1() {
    let mut a = 6;
    let x = reborrow_u32(&mut a);
    assert!(*x == 6);
    *x = 4;
    assert!(a == 4);
}

pub fn test2() {
    let mut a = 6;
    borrow_u32(&mut a);
}

fn test5(x: &mut T, cond: bool) {
    let z = reborrow_T(x);
    let z2;
    if cond {
        z2 = reborrow_T(z);
    } else {
        z2 = reborrow_T(x);
    }
    z2.f = 4;
}

pub struct ListNode {
    next: Option<Box<ListNode>>,
}

fn use_list(_list: &mut ListNode) {}

pub fn test3(list: &mut ListNode) -> &mut ListNode {
    match list.next {
        Some(box ref mut node) => test3(node),
        None => list,
    }
}

pub fn test4(list: &mut ListNode) {
    let last = match list.next {
        Some(box ref mut node) => node,
        None => list,
    };
    use_list(last);
}

fn main() {}
