//https://codeforces.com/blog/entry/20935

#![feature(box_patterns)]
#![feature(box_syntax)]

use prusti_contracts::*;
use std::ptr;

pub struct Tree {
    n: isize,
    idx: isize,
    coins: isize,
    left: Option<Box<Tree>>,
    right: Option<Box<Tree>>,
}

impl Tree {
    #[trusted]
    #[pure]
    #[ensures (result == self.coins)]
    pub fn coins(&self) -> isize {
        self.coins
    }

    #[trusted]
    #[pure]
    #[ensures (result == self.idx)]
    #[ensures(result >= 0 && result < self.n)]
    pub fn idx(&self) -> isize {
        self.idx
    }

    #[trusted]
    #[requires(i  >=  0  && i < nn)]
    #[ensures (result.coins() == c)]
    #[ensures (result.idx() == i)]
    #[ensures(same_n(&result))]
    pub fn new(
        nn: isize,
        i: isize,
        c: isize,
        l: Option<Box<Tree>>,
        r: Option<Box<Tree>>,
    ) -> Self {
        Tree {
            n: nn,
            idx: i,
            coins: c,
            left: l,
            right: r,
        }
    }
}

#[pure]
pub fn same_n(node: &Tree) -> bool {
    let mut result = true;
    match &(*node).left {
        None => {}
        Some(box l) => {
            result &= same_n(&l);
            result &= (node.n == l.n);
        }
    }

    match &(*node).right {
        None => {}
        Some(box r) => {
            result &= same_n(&r);
            result &= (node.n == r.n);
        }
    }
    result
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

#[pure]
#[ensures(result == a - 1)]
fn dec(a: isize) -> isize {
    a - 1
}

#[trusted]
#[pure]
#[ensures(x == y)]
fn is_eq(x: isize, y: isize) -> bool {
    true
}

#[pure]
fn solve1_rec(node: &Tree) -> isize {
    let mut result = node.coins;
    match &(*node).left {
        None => {}
        Some(box l) => {
            result += solve2_rec(&l);
        }
    }

    match &(*node).right {
        None => {}
        Some(box r) => {
            result += solve2_rec(&r);
        }
    }
    result
}

#[pure]
fn solve2_rec(node: &Tree) -> isize {
    let mut result = 0isize;
    match &(*node).left {
        None => {}
        Some(box l) => {
            result += max(solve1_rec(&l), solve2_rec(&l));
        }
    }

    match &(*node).right {
        None => {}
        Some(box r) => {
            result += max(solve1_rec(&r), solve2_rec(&r));
        }
    }
    result
}

#[requires(n > 0)]
#[requires(node.n == n)]
#[requires(dp1.len() == n)]
#[requires(dp2.len() == n)]
#[requires(node.idx() >= 0 && node.idx() < dp1.len())]
#[requires(same_n(node))]
#[ensures(dp1.len() == n)]
#[ensures(dp2.len() == n)]
#[ensures(dp1.lookup(node.idx()) == solve1_rec(node))]
#[ensures(dp2.lookup(node.idx()) == solve2_rec(node))]
fn solve(
    node: &Tree,
    dp1: &mut VecWrapperI32,
    dp2: &mut VecWrapperI32,
    n: isize,
) {
    let mut result1 = node.coins;
    let mut result2 = 0isize;

    match &(*node).left {
        None => {}
        Some(box l) => {
            solve(&l, dp1, dp2, n);
            result1 += dp2.lookup(l.idx());
            result2 += max(dp1.lookup(l.idx()), dp2.lookup(l.idx()));
        }
    }

    match &(*node).right {
        None => {}
        Some(box r) => {
            solve(&r, dp1, dp2, n);
            result1 += dp2.lookup(r.idx());
            result2 += max(dp1.lookup(r.idx()), dp2.lookup(r.idx()));
        }
    }

    dp1.set(node.idx(), result1);
    dp2.set(node.idx(), result2);
}

fn main() {}
