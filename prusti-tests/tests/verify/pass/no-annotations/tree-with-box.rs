//! Currently unsupported because `Box` and `Option` use a type parameter

#![feature(box_patterns)]

struct Tree {
    val: i32,
    left: Option<Box<Tree>>,
    right: Option<Box<Tree>>,
}

fn take_left(tree: Tree) -> Option<Tree> {
    match tree.left {
        Some(box left) => Some(left),
        None => None,
    }
}

fn main() {}
