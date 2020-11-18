//https://onlinejudge.org/index.php?option=com_onlinejudge&Itemid=8&category=24&page=show_problem&problem=1625
use prusti_contracts::*;

pub struct VecWrapperI32 {
    v: Vec<i32>,
}

impl VecWrapperI32 {
    #[trusted]
    #[pure]
    #[ensures (0 <= result)]
    pub fn len(&self) -> usize {
        self.v.len()
    }

    #[trusted]
    #[ensures (result.len() == 0)]
    pub fn new() -> Self {
        VecWrapperI32 { v: Vec::new() }
    }

    #[trusted]
    #[pure]
    #[requires (0 <= index && index < self.len())]
    pub fn lookup(&self, index: usize) -> i32 {
        self.v[index]
    }

    #[trusted]
    #[ensures (self.len() == old(self.len()) + 1)]
    #[ensures (self.lookup(old(self.len())) == value)]
    #[ensures (forall(|i: usize| (0 <= i && i < old(self.len())) ==>
                    self.lookup(i) == old(self.lookup(i))))]
    pub fn push(&mut self, value: i32) {
        self.v.push(value);
    }
}

#[pure]
#[ensures (result >= a && result >= b)]
#[ensures (result == a || result == b)]
fn max(a: i32, b: i32) -> i32 {
    if a < b {
        b
    } else {
        a
    }
}

#[pure]
#[requires (i >= 0)]
#[requires (i < seq.len())]
#[requires (seq.len() > 0)]
fn solve_rec(seq: &VecWrapperI32, i: usize) -> i32 {
    if i == 0 {
        seq.lookup(0)
    } else {
        let prev = solve_rec(seq, i - 1);
        if prev > 0 {
            prev + seq.lookup(i)
        } else {
            seq.lookup(i)
        }
    }
}

#[pure]
#[requires (seq.len() > 0)]
#[requires (idx >= 0)]
#[requires (idx < seq.len())]
fn the_jackpot_rec(seq: &VecWrapperI32, idx: usize) -> i32 {
    if idx == 0 {
        max(0, solve_rec(seq, idx))
    }else {
        max(solve_rec(seq, idx), the_jackpot_rec(seq, idx - 1))
    }
}

// Soluttion >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

#[requires (seq.len() > 0)]
#[ensures (forall(|k:usize| (k >= 0 && k < seq.len()) ==> (seq.len() == result.len() && result.lookup(k) == solve_rec(seq, k))))]
#[ensures (result.len() == seq.len())]
fn solve(seq: &VecWrapperI32) -> VecWrapperI32 {
    let mut dp = VecWrapperI32::new();
    dp.push(seq.lookup(0));
    let mut i = 1usize;
    let len = seq.len();
    while i < len {
        body_invariant!(i >= 1);
        body_invariant!(i < seq.len());
        body_invariant!(dp.len() == i);
        body_invariant!(forall(|k: usize| (k < i && k >= 0) ==> dp.lookup(k) == solve_rec(seq, k)));
        let prev = dp.lookup(i - 1);
        if prev > 0 {
            dp.push(prev + seq.lookup(i));
        } else {
            dp.push(seq.lookup(i));
        }
        i += 1;
    }
    dp
}

#[requires (seq.len() > 0)]
#[ensures (result == the_jackpot_rec(seq, seq.len() - 1))]
fn the_jackpot(seq: &VecWrapperI32) -> i32 {
    let dp = solve(seq);
    let mut answer = max(seq.lookup(0), 0i32);
    let len = seq.len();
    let mut idx = 1;
    while idx < len  {
        body_invariant!(idx >= 1);
        body_invariant!(idx < len);
        body_invariant!(answer == the_jackpot_rec(seq, idx - 1));
        answer = max(answer, dp.lookup(idx));
        idx+=1;
    }
    answer
}

pub fn main() {
}
