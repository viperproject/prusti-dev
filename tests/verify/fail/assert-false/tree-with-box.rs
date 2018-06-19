//! Currently unsupported because `Box` and `Option` use a type parameter

#![feature(nll)]
#![feature(box_patterns)]

// error-pattern: error[P0003]

extern crate prusti_contracts;

struct Tree {
    val: i32,
    left: Option<Box<Tree>>,
    right: Option<Box<Tree>>,
}

fn take_left(tree: Tree) -> Option<Tree> {
    let ret = match tree.left {
        Some(box left) => Some(left),
        None => None,
    };
    assert!(false);
    ret
}

fn main() {}
