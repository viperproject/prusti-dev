// This file contains all the examples from the proposal how to fix #133.

#![feature(box_patterns)]

use prusti_contracts::*;

pub struct T { f: u32, }
pub struct U { f: T, g: T, h: T, }

pub struct ListNode {
    value: U,
    next: Option<Box<ListNode>>,
}

fn consume_t(_a: T) {}
fn consume_u(_a: U) {}
fn use_list_node(_x: &mut ListNode) {}

/// In this example, without consulting the DAG we would restore
/// permissions that were actually dropped:
pub fn test1(cond1: bool, b: U) {
    let mut a = b;
    let x;
    if cond1 {
        x = &mut a.f;
    } else {
        x = &mut a.h;
    }
    x.f = 5;
    consume_u(a);
}

/*
pub fn test2(cond1: bool, mut a: ListNode) {
    let mut x = &mut a;
    if cond1 {
        let y = match x.next {
            Some(box ref mut node) => node,
            None => x,
        };
        x = match y.next {
            Some(box ref mut node) => node,
            None => y,
        };
    } // a.value is dropped during the merge.
    use_list_node(x);
    consume_u(a.value);
}
*/

pub fn test2_1(cond1: bool, mut a: ListNode) {
    let mut x = &mut a;
    let x = match x.next {
        Some(box ref mut node) => node,
        None => x,
    };
    use_list_node(x);
    consume_u(a.value);
}

pub fn test2_2(cond1: bool, mut a: ListNode) {
    let mut x = &mut a;
    if cond1 {
        x = match x.next {
            Some(box ref mut node) => node,
            None => x,
        };
    } // a.value is dropped during the merge.
    x.value.g.f = 4;
}

pub fn test3(cond: bool, b: U) {
    let mut a = b;
    let x;
    if cond {
        x = &mut a.f;
        consume_t(a.g);
    } else {
        x = &mut a.h;
    }
    x.f = 5;
    // x expires here, but we cannot fold a because a.g was moved out.
}

pub fn test4(cond1: bool, cond2: bool, b: U) {
    let mut a = b;
    let x;
    if cond1 {
        x = &mut a.f;
    } else {
        x = &mut a.h;
    }
    if cond2 {
        consume_t(a.g);
    }
    x.f = 5;
    // x expires here, but we cannot fold a because a.g was moved out.
}

pub fn test5(cond1: bool, cond2: bool, mut a: U, mut b: U) {
    let x;
    if cond1 {
        x = &mut a.f;
    } else {
        x = &mut a.h;
    }
    let y;
    if cond2 {
        y = &mut b.f;
    } else {
        y = &mut b.h;
    }
    x.f = 5;
    consume_u(a);
    y.f = 5;
    consume_u(b);
}

fn main() {}
