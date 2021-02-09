#![feature(box_patterns)]
#![feature(box_syntax)]

use prusti_contracts::*;

pub struct Tree {
    n: isize,
    isLucky: bool,
    left: Option<Box<Tree>>,
    right: Option<Box<Tree>>,
}

impl Tree {
    #[trusted]
    #[pure]
    #[ensures (result == self.isLucky)]
    pub fn isLucky(&self) -> bool {
        self.isLucky
    }

    #[trusted]
    #[pure]
    #[ensures (result == self.n)]
    pub fn n(&self) -> isize {
        self.n
    }

    #[trusted]
    #[ensures (result.isLucky() == c)]
    pub fn new(nn: isize, c: bool, l: Option<Box<Tree>>, r: Option<Box<Tree>>) -> Self {
        Tree {
            n: nn,
            isLucky: c,
            left: l,
            right: r,
        }
    }
}

pub struct VecWrapperI32 {
    _ghost_size: usize,
    v: Vec<isize>,
}

impl VecWrapperI32 {
    #[trusted]
    #[pure]
    #[ensures (0 <= result)]
    pub fn len(&self) -> isize {
        self._ghost_size as isize
    }

    #[trusted]
    #[requires(size > 0)]
    #[ensures (result.len() == size)]
    #[ensures (forall(|i: isize| (0 <= i && i < result.len()) ==> result.lookup(i) == 0))]
    pub fn new(size: isize) -> Self {
        Self {
            _ghost_size: size as usize,
            v: vec![0; size as usize],
        }
    }

    #[trusted]
    #[pure]
    #[requires (0 <= index && index < self.len())]
    pub fn lookup(&self, index: isize) -> isize {
        self.v[index as usize]
    }

    #[trusted]
    #[requires(0 <= idx && idx < self.len())]
    #[ensures(self.len() == old(self.len()))]
    #[ensures(self.lookup(idx) == value)]
    #[ensures(forall(|i: isize|
        (0 <= i && i < self.len() && i != idx) ==>
        self.lookup(i) == old(self.lookup(i))))]
    pub fn set(&mut self, idx: isize, value: isize) -> () {
        self.v[idx as usize] = value
    }
}

struct Slice {}

impl Slice {
    #[trusted]
    #[requires(l >= 0)]
    #[ensures(
        result.len() == l &&
        forall(|i: isize| i >= 0 && i < l ==> result.lookup(i) == 0)
    )]
    fn new(l: isize) -> Slice {
        unimplemented!();
    }

    #[trusted]
    #[ensures(
        result.len() == s1.len() + s2.len() &&
        forall(|i: isize| i >= 0 && i < s1.len() ==> s1.lookup(i) == result.lookup(i)) &&
        forall(|i: isize| i >= 0 && i < s2.len() ==> s2.lookup(i) == result.lookup(i + s1.len()))
    )]
    fn append(s1: &Slice, s2: &Slice) -> Slice {
        unimplemented!();
    }

    #[trusted]
    #[requires(l >= 0 && l < self.len())]
    #[requires(r >= l && r <= self.len())]
    #[ensures(
        result.len() == r - l &&
        forall(|i: isize| l <= i && i < r ==>
            result.lookup(i) == self.lookup(i - l))
    )]
    fn split_at(&self, l: isize, r: isize) -> Slice {
        unimplemented!();
    }

    #[trusted]
    #[pure]
    #[requires (0 <= index && index < self.len())]
    pub fn lookup(&self, index: isize) -> isize {
        unimplemented!();
    }

    #[trusted]
    #[requires(0 <= idx && idx < self.len())]
    #[ensures(self.len() == old(self.len()))]
    #[ensures(self.lookup(idx) == value)]
    #[ensures(forall(|i: isize|
        (0 <= i && i < self.len() && i != idx) ==>
        self.lookup(i) == old(self.lookup(i))))]
    pub fn set(&mut self, idx: isize, value: isize) -> () {
        unimplemented!();
    }

    #[trusted]
    #[pure]
    #[ensures (0 <= result)]
    pub fn len(&self) -> isize {
        unimplemented!();
    }
}
#[requires(x.len() == 2)]
#[requires(y.len() == 2)]
#[requires(x.lookup(1) == 3)]
#[requires(x.lookup(1) == 4)]
fn test(x: &Slice, y: &Slice) {
    let z = Slice::append(x, y);
    assert!(z.lookup(1) == 3 && z.lookup(3) == 4);
}

#[pure]
#[ensures(result >  0)]
fn sub_size(node: &Tree) -> isize {
    let mut sz = 1isize;
    match &(*node).left {
        None => {}
        Some(box l) => {
            sz += sub_size(l);
        }
    }

    match &(*node).right {
        None => {}
        Some(box r) => {
            sz += sub_size(r);
        }
    }
    sz
}

#[pure]
#[ensures(node.isLucky() ==> result == sub_size(node))]
#[ensures(!node.isLucky() ==> result == down_lucky(node))]
fn calc_down_lucky(node: &Tree) -> isize {
    if node.isLucky() {
        sub_size(node)
    } else {
        down_lucky(node)
    }
}

#[pure]
fn down_lucky(node: &Tree) -> isize {
    let mut d = 0isize;
    match &(*node).left {
        None => {}
        Some(box l) => {
            d += calc_down_lucky(l);
        }
    }

    match &(*node).right {
        None => {}
        Some(box r) => {
            d += calc_down_lucky(r);
        }
    }
    d
}

#[pure]
#[requires(subSize.len() >= sub_size(node))]
#[requires(leftIdx >= 0 && leftIdx < subSize.len())]
#[requires(rightIdx > leftIdx && rightIdx <= subSize.len())]
#[requires(rightIdx - leftIdx == sub_size(node))]
fn sub_tree_sub_size_computed(
    node: &Tree,
    leftIdx: isize,
    rightIdx: isize,
    subSize: &Slice,
) -> bool {
    let mut result = subSize.lookup(leftIdx) == sub_size(node);
    let mut lIdx = leftIdx + 1;
    let mut rIdx = leftIdx + 1;
    match &(*node).left {
        None => {}
        Some(box l) => {
            let leftSubSize = sub_size(l);
            result = result && sub_tree_sub_size_computed(l, lIdx, lIdx + sub_size(l), subSize);
            rIdx += leftSubSize;
        }
    }

    match &(*node).right {
        None => {}
        Some(box r) => {
            let rightSubSize = sub_size(r);
            result = result && sub_tree_sub_size_computed(r, rIdx, rIdx + rightSubSize, subSize);
        }
    }

    result
}

#[requires(subSize1.len() >= sub_size(node))]
#[requires(subSize2.len() >= sub_size(node))]
#[requires(leftIdx1 >= 0 && leftIdx1 < subSize1.len())]
#[requires(rightIdx1 > leftIdx1 && rightIdx1 <= subSize1.len())]
#[requires(rightIdx1 - leftIdx1 == sub_size(node))]
#[requires(leftIdx2 >= 0 && leftIdx2 < subSize2.len())]
#[requires(rightIdx2 > leftIdx2 && rightIdx2 <= subSize2.len())]
#[requires(rightIdx2 - leftIdx2 == sub_size(node))]
#[requires(forall(|i: isize| (i >= leftIdx1 &&  i < rightIdx1) ==> subSize1.lookup(i) == subSize2.lookup(leftIdx2 + i - leftIdx1)))]
#[requires(sub_tree_sub_size_computed(node, leftIdx2, rightIdx2, subSize2))]
#[ensures(sub_tree_sub_size_computed(node, leftIdx1, rightIdx1, subSize1))]
fn sub_tree_sub_size_computed_helper(
    node: &Tree,
    leftIdx1: isize,
    rightIdx1: isize,
    subSize1: &Slice,
    leftIdx2: isize,
    rightIdx2: isize,
    subSize2: &Slice,
) {
    assert!(subSize1.lookup(leftIdx1) == sub_size(node));
    let mut inc = 1;

    match &(*node).left {
        None => {}
        Some(box l) => {
            let leftSubSize = sub_size(l);
            sub_tree_sub_size_computed_helper(
                l,
                leftIdx1 + inc,
                leftIdx1 + inc + leftSubSize,
                subSize1,
                leftIdx2 + inc,
                leftIdx2 + inc + leftSubSize,
                subSize2,
            );
            inc += leftSubSize;
        }
    }

    match &(*node).right {
        None => {}
        Some(box r) => {
            let rightSubSize = sub_size(r);
            sub_tree_sub_size_computed_helper(
                r,
                leftIdx1 + inc,
                leftIdx1 + inc + rightSubSize,
                subSize1,
                leftIdx2 + inc,
                leftIdx2 + inc + rightSubSize,
                subSize2,
            );
        }
    }
}


