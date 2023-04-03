#![feature(nll)]
#![feature(box_patterns)]

use prusti_contracts::*;

enum List {
    Nil,
    Const {
        val: i32,
        next: Box<List>,
    },
}

fn head(list: List) -> Option<i32> {
    let ret = match list {
        List::Nil => None,
        List::Const { val, box next } => Some(val),
    };
    assert!(false);  //~ ERROR the asserted expression might not hold
    ret
}

fn tail(list: List) -> Option<List> {
    let ret = match list {
        List::Nil => None,
        List::Const { val, box next } => Some(next),
    };
    assert!(false);  //~ ERROR the asserted expression might not hold
    ret
}

fn length(list: List) -> u32 {
    let ret = match list {
        List::Nil => 0,
        List::Const { val, box next } => 1 + length(next),
    };
    assert!(false);  //~ ERROR the asserted expression might not hold
    ret
}

fn last_value(list: List) -> Option<i32> {
    let ret = match list {
        List::Nil => None,
        List::Const { val, box next } => match last_value(next) {
            None => Some(val),
            Some(last) => Some(last),
        }
    };
    assert!(false);  //~ ERROR the asserted expression might not hold
    ret
}

fn empty_list(val: i32) -> List {
    assert!(false);  //~ ERROR the asserted expression might not hold
    List::Nil
}

fn singleton_list(val: i32) -> List {
    let ret = List::Const {
        val,
        next: Box::new(List::Nil),
    };
    assert!(false);  //~ ERROR the asserted expression might not hold
    ret
}

fn prepend(val: i32, list: List) -> List {
    let ret = List::Const {
        val,
        next: Box::new(list),
    };
    assert!(false);  //~ ERROR the asserted expression might not hold
    ret
}

fn append(new_val: i32, list: List) -> List {
    let ret = match list {
        List::Nil => List::Const {
            val: new_val,
            next: Box::new(List::Nil),
        },
        List::Const { val, box next } => List::Const {
            val: val,
            next: Box::new(append(new_val, next)),
        },
    };
    assert!(false);  //~ ERROR the asserted expression might not hold
    ret
}

fn revert(list: List) -> List {
    let ret = match list {
        List::Nil => List::Nil,
        List::Const { val, box next } => append(val, revert(next)),
    };
    assert!(false);  //~ ERROR the asserted expression might not hold
    ret
}

fn main() {}
