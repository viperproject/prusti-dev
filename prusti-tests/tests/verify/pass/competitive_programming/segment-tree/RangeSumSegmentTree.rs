// compile-flags: -Puse_more_complete_exhale=false
// https://codeforces.com/problemset/problem/110/E

#![feature(box_patterns)]
#![feature(box_syntax)]

use prusti_contracts::*;
use std::ptr;

pub struct Tree {
    v: isize,
    left: Option<Box<Tree>>,
    right: Option<Box<Tree>>,
}

impl Tree {
    #[trusted]
    #[pure]
    #[ensures (result == self.v)]
    pub fn v(&self) -> isize {
        self.v
    }

    #[trusted]
    #[ensures (result.v() == vv)]
    pub fn new(vv: isize, l: Option<Box<Tree>>, r: Option<Box<Tree>>) -> Self {
        Tree {
            v: vv,
            left: l,
            right: r,
        }
    }
}

#[pure]
#[ensures(sub_size(node) == 1 ==> result)]
fn is_leaf(node: &Tree) -> bool {
    let mut result = true;

    let tL = &node.left;
    match tL {
        None => {}
        Some(box l) => {
            result = false;
        }
    }

    let tR = &node.right;
    match tR {
        None => {}
        Some(box r) => {
            result = false;
        }
    }

    result
}

#[pure]
#[ensures(result >= 1)]
fn sub_size(node: &Tree) -> isize {
    let mut sz = 1isize;

    let tL = &node.left;
    match tL {
        None => {}
        Some(box l) => {
            sz += sub_size(l);
        }
    }

    let tR = &node.right;
    match tR {
        None => {}
        Some(box r) => {
            sz += sub_size(r);
        }
    }
    sz
}

#[pure]
fn leaves_count(node: &Tree) -> isize {
    if is_leaf(node) {
        1
    } else {
        let mut result = 0;
        let tL = &node.left;
        match tL {
            None => {}
            Some(box l) => {
                result += leaves_count(l);
            }
        }

        let tR = &node.right;
        match tR {
            None => {}
            Some(box r) => {
                result += leaves_count(r);
            }
        }
        result
    }
}

#[pure]
fn is_complete(node: &Tree) -> bool {
    let mut result = true;

    let mut sizeL = 0;
    let mut leavesL = 0;
    let tL = &node.left;
    match tL {
        None => {}
        Some(box l) => {
            result &= is_complete(l);
            sizeL = sub_size(l);
            leavesL = leaves_count(l);
        }
    }

    let tR = &node.right;
    match tR {
        None => {
            result &= sizeL == 0;
        }
        Some(box r) => {
            result &= sub_size(r) == sizeL;
            result &= is_complete(r);
            result &= leaves_count(r) == leavesL;
        }
    }

    result
}

#[pure]
#[requires(is_complete(node))]
#[ensures(result)]
fn ensures_semmetry(node: &Tree) -> bool {
    let mut result = true;
    let size = sub_size(node);
    let leaves = leaves_count(node);

    let mut sizeL = 0;
    let mut leavesL = 0;
    let tL = &node.left;
    match tL {
        None => {}
        Some(box l) => {
            sizeL = sub_size(l);
            leavesL = leaves_count(l);
        }
    }

    let tR = &node.right;
    let mut sizeR = 0;
    let mut leavesR = 0;
    match tR {
        None => {}
        Some(box r) => {
            sizeR = sub_size(r);
            leavesR = leaves_count(r);
        }
    }

    assert!(sizeL == sizeR);
    assert!(leavesL == leavesR);

    let childrenSize = size - 1;
    let childSize = childrenSize / 2;
    assert!(childrenSize == childSize * 2);

    let tL = &node.left;
    match tL {
        None => {}
        Some(box l) => {
            result &= sub_size(l) == childSize;
            let childLeaves = leaves / 2;
            assert!(leaves == childLeaves * 2);
            result &= leaves_count(l) == childLeaves;
        }
    }

    let tR = &node.right;
    let mut sizeR = 0;
    match tR {
        None => {}
        Some(box r) => {
            result &= sub_size(r) == childSize;
            let childLeaves = leaves / 2;
            assert!(leaves == childLeaves * 2);
            result &= leaves_count(r) == childLeaves;
        }
    }

    result
}

#[pure]
fn sum_property(node: &Tree) -> bool {
    if is_leaf(node) {
        true
    } else {
        let mut leaves = 0;
        let mut result = true;
        let tL = &node.left;
        match tL {
            None => {}
            Some(box l) => {
                result &= sum_property(l);
                leaves += l.v();
            }
        }

        let tR = &node.right;
        match tR {
            None => {}
            Some(box r) => {
                result &= sum_property(r);
                leaves += r.v();
            }
        }
        result && leaves == node.v()
    }
}

#[pure]
#[ensures(result <= a && result <= b)]
#[ensures(result == a || result == b)]
fn min(a: isize, b: isize) -> isize {
    if a < b {
        a
    } else {
        b
    }
}

#[pure]
#[ensures(result >= a && result >= b)]
#[ensures(result == a || result == b)]
fn max(a: isize, b: isize) -> isize {
    if a > b {
        a
    } else {
        b
    }
}

#[pure]
#[requires(is_complete(node))]
#[requires(lIdx >= 0 && lIdx < rIdx && rIdx <= leaves_count(node))]
#[requires(ensures_semmetry(node))]
#[requires(leavesCount == leaves_count(node))]
#[requires(sum_property(node))]
#[ensures((lIdx == 0 && rIdx == leavesCount) ==> result == node.v())]
fn sum_of_leaves(node: &Tree, lIdx: isize, rIdx: isize, leavesCount: isize) -> isize {
    if is_leaf(node) {
        assert!(lIdx == 0 && rIdx == leavesCount);
        node.v()
    } else {
        let mut result = 0;

        let midIdx = leavesCount / 2;
        assert!(leaves_count(node) == midIdx * 2);

        let tL = &node.left;
        match tL {
            None => {}
            Some(box l) => {
                if lIdx < midIdx {
                    result += sum_of_leaves(l, lIdx, min(rIdx, midIdx), midIdx);
                } else {
                }
            }
        }

        let tR = &node.right;
        match tR {
            None => {}
            Some(box r) => {
                if rIdx > midIdx {
                    result += sum_of_leaves(r, max(midIdx, lIdx) - midIdx, rIdx - midIdx, midIdx);
                } else {
                }
            }
        }

        result
    }
}

#[pure]
#[requires(is_complete(node))]
#[requires(lIdx >= 0 && lIdx < rIdx && rIdx <= leaves_count(node))]
#[requires(ensures_semmetry(node))]
#[requires(leavesCount == leaves_count(node))]
#[requires(sum_property(node))]
#[ensures(result == sum_of_leaves(node, lIdx, rIdx, leavesCount))]
fn range_sum(node: &Tree, lIdx: isize, rIdx: isize, leavesCount: isize) -> isize {
    if lIdx == 0 && rIdx == leavesCount {
        node.v()
    } else {
        let mut result = 0;

        let midIdx = leavesCount / 2;
        assert!(leaves_count(node) == midIdx * 2);

        let tL = &node.left;
        match tL {
            None => {}
            Some(box l) => {
                if lIdx < midIdx {
                    result += sum_of_leaves(l, lIdx, min(rIdx, midIdx), midIdx);
                } else {
                    result += 0;
                }
            }
        }

        let tR = &node.right;
        match tR {
            None => {}
            Some(box r) => {
                if rIdx > midIdx {
                    result += sum_of_leaves(r, max(midIdx, lIdx) - midIdx, rIdx - midIdx, midIdx);
                } else {
                    result += 0;
                }
            }
        }

        result
    }
}

fn main() {}
