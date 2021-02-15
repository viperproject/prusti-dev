// compile-flags: -Puse_more_complete_exhale=false
// https://codeforces.com/problemset/problem/110/E

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

#[ensures(result.0.len() == sub_size(node))]
#[ensures(result.1.len() == sub_size(node))]
#[ensures(result.0.lookup(0) == sub_size(node))]
#[ensures(result.1.lookup(0) == down_lucky(node))]
#[ensures(sub_tree_sub_size_computed(node, 0, sub_size(node), &result.0))]
#[ensures(sub_tree_down_lucky_computed(node, 0, sub_size(node), &result.1))]
fn dfs1(node: &Tree) -> (Slice, Slice) {
    let answer = &mut VecWrapperI32::new(2);
    let (childrenSubSize, childrenDownLucky) = dfs1_helper(node, answer);
    let mut nodeSubSize = Slice::new(1);
    nodeSubSize.set(0, answer.lookup(0));
    let mut nodeDownLucky = Slice::new(1);
    nodeDownLucky.set(0, answer.lookup(1));
    let subSize = Slice::append(&nodeSubSize, &childrenSubSize);
    let downLucky = Slice::append(&nodeDownLucky, &childrenDownLucky);

    let mut inc = 0;
    let tL = &node.left;
    match tL {
        None => {}
        Some(box l) => {
            assert!(sub_tree_sub_size_computed(
                l,
                0,
                sub_size(l),
                &childrenSubSize
            ));
            sub_tree_sub_size_computed_helper(
                l,
                1,
                1 + sub_size(l),
                &subSize,
                0,
                sub_size(l),
                &childrenSubSize,
            );
            assert!(sub_tree_sub_size_computed(l, 1, 1 + sub_size(l), &subSize));

            assert!(sub_tree_down_lucky_computed(
                l,
                0,
                sub_size(l),
                &childrenDownLucky
            ));
            sub_tree_down_lucky_computed_helper(
                l,
                1,
                1 + sub_size(l),
                &downLucky,
                0,
                sub_size(l),
                &childrenDownLucky,
            );
            assert!(sub_tree_down_lucky_computed(
                l,
                1,
                1 + sub_size(l),
                &downLucky
            ));
            inc += sub_size(l);
        }
    }

    let tR = &node.right;
    match tR {
        None => {}
        Some(box r) => {
            assert!(sub_tree_sub_size_computed(
                r,
                inc,
                inc + sub_size(r),
                &childrenSubSize
            ));
            sub_tree_sub_size_computed_helper(
                r,
                1 + inc,
                1 + inc + sub_size(r),
                &subSize,
                inc,
                inc + sub_size(r),
                &childrenSubSize,
            );
            assert!(sub_tree_sub_size_computed(
                r,
                1 + inc,
                1 + inc + sub_size(r),
                &subSize
            ));

            assert!(sub_tree_down_lucky_computed(
                r,
                inc,
                inc + sub_size(r),
                &childrenDownLucky
            ));
            sub_tree_down_lucky_computed_helper(
                r,
                1 + inc,
                1 + inc + sub_size(r),
                &downLucky,
                inc,
                inc + sub_size(r),
                &childrenDownLucky,
            );
            assert!(sub_tree_down_lucky_computed(
                r,
                1 + inc,
                1 + inc + sub_size(r),
                &downLucky
            ));
        }
    }

    (subSize, downLucky)
}

#[requires(answer.len() == 2)]
#[ensures(answer.len() == old(answer.len()))]
#[ensures(answer.lookup(0) == sub_size(node))]
#[ensures(answer.lookup(1) == down_lucky(node))]
#[ensures(result.0.len() == sub_size(node) - 1)]
#[ensures(result.1.len() == sub_size(node) - 1)]
#[ensures(result.0.len() == sub_size(node) - 1)]
#[ensures(h1(node, &result.0))]
#[ensures(h2(node, &result.1))]
fn dfs1_helper(node: &Tree, answer: &mut VecWrapperI32) -> (Slice, Slice) {
    let mut sz = 1isize;
    let mut d = 0isize;
    let mut leftSubSize = Slice::new(0);
    let mut rightSubSize = Slice::new(0);
    let mut leftDownLucky = Slice::new(0);
    let mut rightDownLucky = Slice::new(0);
    match &(*node).left {
        None => {}
        Some(box l) => {
            let (a, b) = dfs1(l);
            leftSubSize = a;
            leftDownLucky = b;
            if l.isLucky() {
                d += leftSubSize.lookup(0);
            } else {
                d += leftDownLucky.lookup(0);
            }
            sz += leftSubSize.lookup(0);
        }
    }

    match &(*node).right {
        None => {}
        Some(box r) => {
            let (a, b) = dfs1(r);
            rightSubSize = a;
            rightDownLucky = b;
            if r.isLucky() {
                d += rightSubSize.lookup(0);
            } else {
                d += rightDownLucky.lookup(0);
            }
            sz += rightSubSize.lookup(0);
        }
    }

    let subSize = Slice::append(&leftSubSize, &rightSubSize);
    let downLucky = Slice::append(&leftDownLucky, &rightDownLucky);

    answer.set(0, sz);
    answer.set(1, d);
    let mut inc = 0;
    let tL = &node.left;
    match tL {
        None => {}
        Some(box l) => {
            assert!(sub_tree_sub_size_computed(l, 0, sub_size(l), &leftSubSize));
            sub_tree_sub_size_computed_helper(
                l,
                0,
                sub_size(l),
                &subSize,
                0,
                sub_size(l),
                &leftSubSize,
            );
            assert!(sub_tree_sub_size_computed(l, 0, sub_size(l), &subSize));

            assert!(sub_tree_down_lucky_computed(
                l,
                0,
                sub_size(l),
                &leftDownLucky
            ));
            sub_tree_down_lucky_computed_helper(
                l,
                0,
                sub_size(l),
                &downLucky,
                0,
                sub_size(l),
                &leftDownLucky,
            );
            assert!(sub_tree_down_lucky_computed(l, 0, sub_size(l), &downLucky));
            inc += sub_size(l);
        }
    }

    let tR = &node.right;
    match tR {
        None => {}
        Some(box r) => {
            assert!(sub_tree_sub_size_computed(r, 0, sub_size(r), &rightSubSize));
            sub_tree_sub_size_computed_helper(
                r,
                inc,
                inc + sub_size(r),
                &subSize,
                0,
                sub_size(r),
                &rightSubSize,
            );
            assert!(sub_tree_sub_size_computed(
                r,
                inc,
                inc + sub_size(r),
                &subSize
            ));

            assert!(sub_tree_down_lucky_computed(
                r,
                0,
                sub_size(r),
                &rightDownLucky
            ));
            sub_tree_down_lucky_computed_helper(
                r,
                inc,
                inc + sub_size(r),
                &downLucky,
                0,
                sub_size(r),
                &rightDownLucky,
            );
            assert!(sub_tree_down_lucky_computed(
                r,
                inc,
                inc + sub_size(r),
                &downLucky
            ));
        }
    }

    (subSize, downLucky)
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

    let t1 = &node.left;
    match t1 {
        None => {}
        Some(l) => {
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
    let _t = t1;
    let _a = subSize1;
    let _a = subSize2;

    let t = &node.right;
    match t {
        None => {}
        Some(r) => {
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
    let _t = t;
    let _a = subSize1;
    let _a = subSize2;
}

#[pure]
#[requires(subSize.len() == sub_size(node) - 1)]
fn h1(node: &Tree, subSize: &Slice) -> bool {
    let mut result = true;
    let mut lIdx = 0;
    let mut rIdx = 0;
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

#[pure]
#[requires(downLucky.len() >= sub_size(node))]
#[requires(leftIdx >= 0 && leftIdx < downLucky.len())]
#[requires(rightIdx > leftIdx && rightIdx <= downLucky.len())]
#[requires(rightIdx - leftIdx == sub_size(node))]
fn sub_tree_down_lucky_computed(
    node: &Tree,
    leftIdx: isize,
    rightIdx: isize,
    downLucky: &Slice,
) -> bool {
    let mut result = downLucky.lookup(leftIdx) == down_lucky(node);
    let mut lIdx = leftIdx + 1;
    let mut rIdx = leftIdx + 1;
    match &(*node).left {
        None => {}
        Some(box l) => {
            let leftSubSize = sub_size(l);
            result = result && sub_tree_down_lucky_computed(l, lIdx, lIdx + sub_size(l), downLucky);
            rIdx += leftSubSize;
        }
    }

    match &(*node).right {
        None => {}
        Some(box r) => {
            let rightSubSize = sub_size(r);
            result =
                result && sub_tree_down_lucky_computed(r, rIdx, rIdx + rightSubSize, downLucky);
        }
    }

    result
}

#[requires(downLucky1.len() >= sub_size(node))]
#[requires(downLucky2.len() >= sub_size(node))]
#[requires(leftIdx1 >= 0 && leftIdx1 < downLucky1.len())]
#[requires(rightIdx1 > leftIdx1 && rightIdx1 <= downLucky1.len())]
#[requires(rightIdx1 - leftIdx1 == sub_size(node))]
#[requires(leftIdx2 >= 0 && leftIdx2 < downLucky2.len())]
#[requires(rightIdx2 > leftIdx2 && rightIdx2 <= downLucky2.len())]
#[requires(rightIdx2 - leftIdx2 == sub_size(node))]
#[requires(forall(|i: isize| (i >= leftIdx1 &&  i < rightIdx1) ==> downLucky1.lookup(i) == downLucky2.lookup(leftIdx2 + i - leftIdx1)))]
#[requires(sub_tree_down_lucky_computed(node, leftIdx2, rightIdx2, downLucky2))]
#[ensures(sub_tree_down_lucky_computed(node, leftIdx1, rightIdx1, downLucky1))]
fn sub_tree_down_lucky_computed_helper(
    node: &Tree,
    leftIdx1: isize,
    rightIdx1: isize,
    downLucky1: &Slice,
    leftIdx2: isize,
    rightIdx2: isize,
    downLucky2: &Slice,
) {
    assert!(downLucky1.lookup(leftIdx1) == down_lucky(node));
    let mut inc = 1;

    let t1 = &node.left;
    match t1 {
        None => {}
        Some(l) => {
            let leftSubSize = sub_size(l);
            sub_tree_down_lucky_computed_helper(
                l,
                leftIdx1 + inc,
                leftIdx1 + inc + leftSubSize,
                downLucky1,
                leftIdx2 + inc,
                leftIdx2 + inc + leftSubSize,
                downLucky2,
            );
            inc += leftSubSize;
        }
    }
    let _t = t1;
    let _a = downLucky1;
    let _a = downLucky2;

    let t = &node.right;
    match t {
        None => {}
        Some(r) => {
            let rightSubSize = sub_size(r);
            sub_tree_down_lucky_computed_helper(
                r,
                leftIdx1 + inc,
                leftIdx1 + inc + rightSubSize,
                downLucky1,
                leftIdx2 + inc,
                leftIdx2 + inc + rightSubSize,
                downLucky2,
            );
        }
    }
    let _t = t;
    let _a = downLucky1;
    let _a = downLucky2;
}

#[pure]
#[requires(downLucky.len() == sub_size(node) - 1)]
fn h2(node: &Tree, downLucky: &Slice) -> bool {
    let mut result = true;
    let mut lIdx = 0;
    let mut rIdx = 0;
    match &(*node).left {
        None => {}
        Some(box l) => {
            let leftSubSize = sub_size(l);
            result = result && sub_tree_down_lucky_computed(l, lIdx, lIdx + sub_size(l), downLucky);
            rIdx += leftSubSize;
        }
    }

    match &(*node).right {
        None => {}
        Some(box r) => {
            let rightSubSize = sub_size(r);
            result =
                result && sub_tree_down_lucky_computed(r, rIdx, rIdx + rightSubSize, downLucky);
        }
    }

    result
}

#[pure]
fn dfs2_compute_left(node: &Tree, x1: isize, x2: isize) -> isize {
    match &(*node).left {
        None => 0,
        Some(box l) => {
            if l.isLucky() {
                dfs2_compute(l, x1)
            } else {
                dfs2_compute(l, x2 - down_lucky(l))
            }
        }
    }
}

#[pure]
fn dfs2_compute_right(node: &Tree, x1: isize, x2: isize) -> isize {
    match &(*node).right {
        None => 0,
        Some(box r) => {
            if r.isLucky() {
                dfs2_compute(r, x1)
            } else {
                dfs2_compute(r, x2 - down_lucky(r))
            }
        }
    }
}

#[pure]
fn dfs2_compute(node: &Tree, upLucky: isize) -> isize {
    let d1 = down_lucky(node);
    let tot = upLucky + d1;
    let mut result = tot * (tot - 1);
    let x1 = node.n() - sub_size(node);
    let x2 = upLucky + down_lucky(node);
    result += dfs2_compute_left(node, x1, x2);
    result += dfs2_compute_right(node, x1, x2);
    result
}

#[requires(subSize.len() == downLucky.len())]
#[requires(subSize.len() >= sub_size(node))]
#[requires(leftIdx >= 0 && leftIdx < subSize.len())]
#[requires(rightIdx > leftIdx && rightIdx <= subSize.len())]
#[requires(rightIdx - leftIdx == sub_size(node))]
#[requires(sub_tree_sub_size_computed(node, leftIdx, rightIdx, subSize))]
#[requires(sub_tree_down_lucky_computed(node, leftIdx, rightIdx, downLucky))]
#[ensures(result == dfs2_compute_left(node, x1, x2))]
fn dfs2_left(
    node: &Tree,
    leftIdx: isize,
    rightIdx: isize,
    subSize: &Slice,
    downLucky: &Slice,
    x1: isize,
    x2: isize,
) -> isize {

    let mut resultL = 0;

    let lT = &node.left;
    let mut lSize = 0;
    match lT {
        None => {}
        Some(box l) => {
            lSize = subSize.lookup(leftIdx + 1);
            assert!(sub_tree_sub_size_computed(
                l,
                leftIdx + 1,
                leftIdx + 1 + sub_size(l),
                &subSize
            ));
            assert!(lSize == sub_size(l));
            assert!(sub_tree_down_lucky_computed(
                l,
                leftIdx + 1,
                leftIdx + 1 + sub_size(l),
                &downLucky
            ));
            assert!(downLucky.lookup(leftIdx + 1) == down_lucky(l));

            if l.isLucky() {
                assert!(dfs2(
                    l,
                    leftIdx + 1,
                    leftIdx + 1 + lSize,
                    x1,
                    subSize,
                    downLucky,
                ) == dfs2_compute(l, x1));
                resultL += dfs2(
                    l,
                    leftIdx + 1,
                    leftIdx + 1 + lSize,
                    x1,
                    subSize,
                    downLucky,
                );
            } else {
                assert!(dfs2(
                    l,
                    leftIdx + 1,
                    leftIdx + 1 + lSize,
                    x2 - downLucky.lookup(leftIdx + 1),
                    subSize,
                    downLucky,
                ) == dfs2_compute(l, x2 - down_lucky(l)));
                resultL += dfs2(
                    l,
                    leftIdx + 1,
                    leftIdx + 1 + lSize,
                    x2 - downLucky.lookup(leftIdx + 1),
                    subSize,
                    downLucky,
                );
            }
        }
    }


    let _t = lT;
    let _a = subSize;
    let _b = downLucky;

    resultL
}

#[requires(subSize.len() == downLucky.len())]
#[requires(subSize.len() >= sub_size(node))]
#[requires(leftIdx >= 0 && leftIdx < subSize.len())]
#[requires(rightIdx > leftIdx && rightIdx <= subSize.len())]
#[requires(rightIdx - leftIdx == sub_size(node))]
#[requires(sub_tree_sub_size_computed(node, leftIdx, rightIdx, subSize))]
#[requires(sub_tree_down_lucky_computed(node, leftIdx, rightIdx, downLucky))]
#[ensures(result == dfs2_compute_right(node, x1, x2))]
fn dfs2_right(
    node: &Tree,
    leftIdx: isize,
    rightIdx: isize,
    subSize: &Slice,
    downLucky: &Slice,
    x1: isize,
    x2: isize,
) -> isize {

    let lT = &node.left;
    let mut lSize = 0;
    match lT {
        None => {}
        Some(box l) => {
            lSize = subSize.lookup(leftIdx + 1);
            assert!(sub_tree_sub_size_computed(
                l,
                leftIdx + 1,
                leftIdx + 1 + sub_size(l),
                &subSize
            ));
            assert!(lSize == sub_size(l));
        }
    }

    let mut resultR = 0;

    let rT = &node.right;
    let mut rSize = 0;
    match rT {
        None => {}
        Some(box r) => {
            rSize = subSize.lookup(leftIdx + 1 + lSize);
            assert!(sub_tree_sub_size_computed(
                r,
                leftIdx + 1 + lSize,
                leftIdx + 1 + lSize + sub_size(r),
                &subSize
            ));
            assert!(rSize == sub_size(r));
            assert!(sub_tree_down_lucky_computed(
                r,
                leftIdx + 1 + lSize,
                leftIdx + 1 + lSize + sub_size(r),
                &downLucky
            ));
            assert!(downLucky.lookup(leftIdx + 1 + lSize) == down_lucky(r));
            if r.isLucky() {
                assert!(dfs2(
                    r,
                    leftIdx + 1 + lSize,
                    leftIdx + 1 + lSize + rSize,
                    x1,
                    subSize,
                    downLucky,
                )  == dfs2_compute(r, x1));
                resultR += dfs2(
                    r,
                    leftIdx + 1 + lSize,
                    leftIdx + 1 + lSize + rSize,
                    x1,
                    subSize,
                    downLucky,
                );
            } else {
                assert!(dfs2(
                    r,
                    leftIdx + 1 + lSize,
                    leftIdx + 1 + lSize + rSize,
                    x2 - downLucky.lookup(leftIdx + 1 + lSize),
                    subSize,
                    downLucky,
                ) == dfs2_compute(r, x2 - down_lucky(r)));
                resultR += dfs2(
                    r,
                    leftIdx + 1 + lSize,
                    leftIdx + 1 + lSize + rSize,
                    x2 - downLucky.lookup(leftIdx + 1 + lSize),
                    subSize,
                    downLucky,
                );
            }
        }
    }

    let _t = rT;
    let _a = subSize;
    let _b = downLucky;

    resultR
}

#[requires(subSize.len() == downLucky.len())]
#[requires(subSize.len() >= sub_size(node))]
#[requires(leftIdx >= 0 && leftIdx < subSize.len())]
#[requires(rightIdx > leftIdx && rightIdx <= subSize.len())]
#[requires(rightIdx - leftIdx == sub_size(node))]
#[requires(sub_tree_sub_size_computed(node, leftIdx, rightIdx, subSize))]
#[requires(sub_tree_down_lucky_computed(node, leftIdx, rightIdx, downLucky))]
#[ensures(result == dfs2_compute(node, upLucky))]
fn dfs2(
    node: &Tree,
    leftIdx: isize,
    rightIdx: isize,
    upLucky: isize,
    subSize: &Slice,
    downLucky: &Slice,
) -> isize {

    let d1 = downLucky.lookup(leftIdx);
    assert!(d1 == down_lucky(node));
    let tot = upLucky + d1;
    let mut result = tot * (tot - 1);
    let s1 = subSize.lookup(leftIdx);
    assert!(s1 == sub_size(node));
    let x1 = node.n() - s1;
    let x2 = upLucky + d1;
    let resultL = dfs2_left(node, leftIdx, rightIdx, subSize, downLucky, x1, x2);
    let resultR = dfs2_right(node, leftIdx, rightIdx, subSize, downLucky, x1, x2);
    assert!(resultL == dfs2_compute_left(node, x1, x2));
    assert!(resultR == dfs2_compute_right(node, x1, x2));
    result += resultL;
    result += resultR;
    result
}

#[ensures(result == dfs2_compute(node, 0))]
fn solve(node: &Tree) -> isize {
    let (subSize, downLucky) = dfs1(node);
    dfs2(node, 0, subSize.lookup(0), 0isize, &subSize, &downLucky)
}

fn main() {}
