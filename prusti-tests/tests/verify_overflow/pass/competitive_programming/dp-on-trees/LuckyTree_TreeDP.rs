// compile-flags: -Passert_timeout=120000
// https://codeforces.com/blog/entry/20935

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

#[trusted]
#[ensures(false)]
fn assume_false() {}

#[ensures(node.n() == old(node.n()))]
#[ensures(node.isLucky() == old(node.isLucky()))]
#[ensures(node.dp1() == sub_size(node))]
#[ensures(node.dp2() == down_lucky(node))]
fn dfs1(node: &mut Tree) {
    let answer = &mut VecWrapperI32::new(2);

    helper(node, answer);

    assert!(answer.lookup(0) == sub_size(node));
    assert!(answer.lookup(1) == down_lucky(node));
    node.set_dp1(answer.lookup(0));
    assert!(node.dp1() == sub_size(node));
    node.set_dp2(answer.lookup(1));
    assert!(node.dp1() == sub_size(node));
    assert!(node.dp2() == down_lucky(node));
}

#[requires(answer.len() == 2)]
#[ensures(answer.len() == old(answer.len()))]
#[ensures(answer.lookup(0) == sub_size(node))]
#[ensures(answer.lookup(1) == down_lucky(node))]
fn helper(node: &mut Tree, answer: &mut VecWrapperI32)  {
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
