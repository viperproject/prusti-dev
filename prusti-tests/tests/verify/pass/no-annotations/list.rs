//! Example of linked list

#![feature(box_patterns)]

enum List {
    Nil,
    Const {
        val: i32,
        next: Box<List>,
    },
}

fn head(list: List) -> Option<i32> {
    match list {
        List::Nil => None,
        List::Const { val, box next } => Some(val),
    }
}

fn tail(list: List) -> Option<List> {
    match list {
        List::Nil => None,
        List::Const { val, box next } => Some(next),
    }
}

fn length(list: List) -> u32 {
    match list {
        List::Nil => 0,
        List::Const { val, box next } => 1 + length(next),
    }
}

fn last_value(list: List) -> Option<i32> {
    match list {
        List::Nil => None,
        List::Const { val, box next } => match last_value(next) {
            None => Some(val),
            Some(last) => Some(last),
        }
    }
}

fn empty_list(val: i32) -> List {
    List::Nil
}

fn singleton_list(val: i32) -> List {
    List::Const {
        val,
        next: Box::new(List::Nil),
    }
}

fn prepend(val: i32, list: List) -> List {
    List::Const {
        val,
        next: Box::new(list),
    }
}

fn append(new_val: i32, list: List) -> List {
    match list {
        List::Nil => List::Const {
            val: new_val,
            next: Box::new(List::Nil),
        },
        List::Const { val, box next } => List::Const {
            val: val,
            next: Box::new(append(new_val, next)),
        },
    }
}

fn revert(list: List) -> List {
    match list {
        List::Nil => List::Nil,
        List::Const { val, box next } => append(val, revert(next))
    }
}

fn main() {}
