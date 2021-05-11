// compile-flags: -Puse_more_complete_exhale=false -Passert_timeout=1200000
// https://codeforces.com/problemset/problem/110/E

#![feature(box_patterns)]
#![feature(box_syntax)]

use prusti_contracts::*;
use std::ptr;

pub struct Tree {
    n: isize,
    isLucky: bool,
    dp1: isize,
    dp2: isize,
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
            dp1: 0,
            dp2: 0,
            left: l,
            right: r,
        }
    }

    #[pure]
    #[ensures (result == self.dp1)]
    pub fn dp1(&self) -> isize {
        self.dp1
    }

    #[ensures(self.n() == old(self.n()))]
    #[ensures(self.isLucky() == old(self.isLucky()))]
    #[ensures(self.dp2() == old(self.dp2()))]
    #[ensures(self.dp1() == v)]
    #[ensures(sub_size(self) == old(sub_size(self)))]
    #[ensures(down_lucky(self) == old(down_lucky(self)))]
    #[ensures(h1(self) == old(h1(self)))]
    #[ensures(h2(self) == old(h2(self)))]
    #[ensures(sub_tree_down_lucky_computed(self) == old(sub_tree_down_lucky_computed(self)))]
    pub fn set_dp1(&mut self, v: isize) {
        self.dp1 = v;
    }

    #[pure]
    #[ensures (result == self.dp2)]
    pub fn dp2(&self) -> isize {
        self.dp2
    }

    #[ensures(self.dp2() == v)]
    #[ensures(self.n() == old(self.n()))]
    #[ensures(self.isLucky() == old(self.isLucky()))]
    #[ensures(self.dp1() == old(self.dp1()))]
    #[ensures(sub_size(self) == old(sub_size(self)))]
    #[ensures(down_lucky(self) == old(down_lucky(self)))]
    #[ensures(h1(self) == old(h1(self)))]
    #[ensures(h2(self) == old(h2(self)))]
    #[ensures(sub_tree_sub_size_computed(self) == old(sub_tree_sub_size_computed(self)))]
    pub fn set_dp2(&mut self, v: isize) {
        self.dp2 = v;
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

#[pure]
#[ensures (result >= a && result >= b)]
#[ensures (result == a || result == b)]
fn max(a: isize, b: isize) -> isize {
    if a > b {
        a
    } else {
        b
    }
}

#[trusted]
#[pure]
#[ensures(result == a + b)]
fn add(a: isize, b: isize) -> isize {
    a + b
}

// Naive Solution

#[pure]
fn sub_size(node: &Tree) -> isize {
    let mut sz = 1isize;
    match &node.left {
        None => {}
        Some(box l) => {
            sz += sub_size(l);
        }
    }

    match &node.right {
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
    match &node.left {
        None => {}
        Some(box l) => {
            d += calc_down_lucky(l);
        }
    }

    match &node.right {
        None => {}
        Some(box r) => {
            d += calc_down_lucky(r);
        }
    }
    d
}

#[ensures(node.n() == old(node.n()))]
#[ensures(node.isLucky() == old(node.isLucky()))]
#[ensures(sub_tree_sub_size_computed(node))]
#[ensures(sub_tree_down_lucky_computed(node))]
fn dfs1(node: &mut Tree) {
    let answer = &mut VecWrapperI32::new(2);
    helper(node, answer);
    node.set_dp1(answer.lookup(0));
    node.set_dp2(answer.lookup(1));
}

#[requires(answer.len() == 2)]
#[ensures(answer.len() == old(answer.len()))]
#[ensures(answer.lookup(0) == sub_size(node))]
#[ensures(answer.lookup(1) == down_lucky(node))]
#[ensures(node.n() == old(node.n()))]
#[ensures(node.isLucky() == old(node.isLucky()))]
#[ensures(match &node.left {
    None => {true}
    Some(box l) => {
        sub_tree_sub_size_computed(l) && sub_tree_down_lucky_computed(l)
    }
})]
#[ensures(match &node.right {
    None => {true}
    Some(box r) => {
        sub_tree_sub_size_computed(r) && sub_tree_down_lucky_computed(r)
    }
})]
fn helper(node: &mut Tree, answer: &mut VecWrapperI32) {
    let mut sz = 1isize;
    let mut d = 0isize;

    match &mut node.left {
        None => {}
        Some(box l) => {
            dfs1(l);
            if l.isLucky() {
                d += l.dp1();
            } else {
                d += l.dp2();
            }
            sz += l.dp1();
        }
    }

    match &mut node.right {
        None => {}
        Some(box r) => {
            dfs1(r);
            if r.isLucky() {
                d += r.dp1();
            } else {
                d += r.dp2();
            }
            sz += r.dp1();
        }
    }
    answer.set(0, sz);
    answer.set(1, d);
}

#[pure]
fn sub_tree_sub_size_computed(node: &Tree) -> bool {
    let mut result = node.dp1() == sub_size(node);
    match &(*node).left {
        None => {}
        Some(box l) => {
            result = result && sub_tree_sub_size_computed(l);
        }
    }

    match &(*node).right {
        None => {}
        Some(box r) => {
            result = result && sub_tree_sub_size_computed(r);
        }
    }

    result
}

#[pure]
fn h1(node: &Tree) -> bool {
    let mut result = true;
    match &(*node).left {
        None => {}
        Some(box l) => {
            result = result && sub_tree_sub_size_computed(l);
        }
    }

    match &(*node).right {
        None => {}
        Some(box r) => {
            result = result && sub_tree_sub_size_computed(r);
        }
    }

    result
}

#[pure]
fn sub_tree_down_lucky_computed(node: &Tree) -> bool {
    let mut result = node.dp2() == down_lucky(node);
    match &(*node).left {
        None => {}
        Some(box l) => {
            result = result && sub_tree_down_lucky_computed(l);
        }
    }

    match &(*node).right {
        None => {}
        Some(box r) => {
            result = result && sub_tree_down_lucky_computed(r);
        }
    }

    result
}

#[pure]
fn h2(node: &Tree) -> bool {
    let mut result = true;
    match &(*node).left {
        None => {}
        Some(box l) => {
            result = result && sub_tree_down_lucky_computed(l);
        }
    }

    match &(*node).right {
        None => {}
        Some(box r) => {
            result = result && sub_tree_down_lucky_computed(r);
        }
    }

    result
}

#[pure]
fn dfs2_compute_left(node: &Tree, x1: isize, x2: isize) -> isize {
    match &(*node).left {
        None => {
            0
        }
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
        None => {
            0
        }
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

#[requires(sub_tree_sub_size_computed(node))]
#[requires(sub_tree_down_lucky_computed(node))]
#[ensures(result == dfs2_compute(node, upLucky))]
fn dfs2(node: &Tree, upLucky: isize) -> isize {
    let d1 = node.dp2();
    let tot = upLucky + d1;
    let mut result = tot * (tot - 1);
    match &(*node).left {
        None => {}
        Some(box l) => {
            if l.isLucky() {
                result += dfs2(l, node.n - node.dp1);
            } else {
                result += dfs2(l, upLucky + d1 - l.dp2());
            }
        }
    }

    match &(*node).right {
        None => {}
        Some(box r) => {
            if r.isLucky() {
                result += dfs2(r, node.n - node.dp1());
            } else {
                result += dfs2(r, upLucky + d1 - r.dp2());
            }
        }
    }
    result
}
 
#[ensures(result == dfs2_compute(node, 0))]
fn solve(node: &mut Tree) -> isize {
    dfs1(node);
    dfs2(node, 0isize)
}

fn main() {}
