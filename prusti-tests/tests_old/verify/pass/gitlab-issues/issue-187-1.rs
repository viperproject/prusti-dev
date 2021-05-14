#![feature(box_patterns, box_syntax)]

use prusti_contracts::*;

type Triple = (i32, i32, i32);

struct List {
    next: Option<Box<List>>,
    elem: Triple
}

#[pure]
fn contains(list: &List, i: i32, j: i32) -> bool {
    if list.elem.0 == i && list.elem.1 == j {
        true
    } else {
        match list.next {
            Some(box ref tail) => contains(tail, i, j),
            None => false
        }
    }
}

#[requires(!contains(list, elem.0, elem.1))]
#[ensures(contains(list, elem.0, elem.1))]
#[ensures(forall(|i: i32, j: i32| old(contains(list, i, j)) ==> contains(list, i, j)))]
#[ensures(forall(|i: i32, j: i32| (!old(contains(list, i, j)) && i != elem.0 && j != elem.1) ==> !contains(list, i, j)))]
fn append(list: &mut List, elem: Triple) {
    match list.next {
        Some(box ref mut tail) => append(tail, elem),
        None => {
            list.next = Some(
                box List {
                    next: None,
                    elem: elem
                }
            )
        }
    }
}

fn main() {}
