#![feature(nll)]
#![feature(box_patterns)]

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
    assert!(false);  //~ ERROR assert!(..) statement might not hold
    ret
}

fn main() {}
