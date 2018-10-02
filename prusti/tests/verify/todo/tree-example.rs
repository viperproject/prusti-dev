#![feature(nll)]
#![feature(box_patterns)]
#![feature(box_syntax)]

extern crate prusti_contracts;

use std::borrow::BorrowMut;

struct Tree {
    value: u32,
    left: Option<Box<Tree>>,
    right: Option<Box<Tree>>,
}

/// Inserts a value in a binary search tree. Recursive implementation.
fn recursive_insert(root: &mut Tree, new_value: u32) {
    let target = if new_value < root.value {
        &mut root.left
    } else {
        &mut root.right
    };
    match target {
        &mut None => *target = Some(box Tree {
            value: new_value,
            left: None,
            right: None
        }),
        &mut Some(box ref mut subtree) => recursive_insert(subtree, new_value)
    }
}

/// Inserts a value in a binary search tree. Iterative implementation.
fn iterative_insert(root: &mut Tree, new_value: u32) {
    let mut curr = if new_value < root.value {
        &mut root.left
    } else {
        &mut root.right
    };
    while curr.is_some() {
        curr = match curr {
            &mut None => unreachable!(),
            &mut Some(box ref mut subtree) => if new_value < subtree.value {
                &mut subtree.left
            } else {
                &mut subtree.right
            }
        }
    }
    assert!(curr.is_none());
    *curr = Some(box Tree {
        value: new_value,
        left: None,
        right: None
    });
}

fn main() {}
